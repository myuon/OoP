{-# LANGUAGE Rank2Types #-}
module Battle (
  ix,
  ixM,
  ixIM,

  BattleState(..),
  Board (Board),
  Tactic,
  TacticList,
  addTactic,
  runBoard,
  player,
  enemy,
  turn,
  tacticList,
  battleState,

  module Character
) where

import Control.Arrow
import Control.Monad.State
import Data.List
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Lens.Family2
import Lens.Family2.State.Lazy
import Lens.Family2.Unchecked

import Character

ix :: Int -> Lens' [a] a
ix n = lens (!! n) (\l x -> take (n-1) l ++ [x] ++ drop (n+1) l)

ixM :: (Ord a) => a -> Lens' (M.Map a b) b
ixM n = lens (M.! n) (\l x -> M.insert n x l)

ixIM :: Int -> Lens' (IM.IntMap b) b
ixIM n = lens (IM.! n) (\l x -> IM.insert n x l)

getCommand :: CommandList -> (Command, CommandList)
getCommand cl = ((cl ^. commandMap) IM.! (cl ^. index), cl & index .~ nextIndex) where
  nextIndex = if (cl^.index) == (cl^.listSize) - 1 then 0 else cl^.index + 1

type Tactic = M.Map String CommandList
type TacticList = IM.IntMap Tactic

addTactic :: Tactic -> TacticList -> TacticList
addTactic x tt = IM.insert (mi + 1) x tt where
  mi = maximum $ IM.keys tt

data BattleState = Waiting | Win | Lose | Battling deriving (Eq, Show)

data Board = Board {
  _player :: [Character],
  _enemy :: [Character],
  _turn :: Int,
  _tacticList :: TacticList,
  _battleState :: BattleState
} deriving (Show)

player :: Lens' Board [Character]
player = lens _player (\f x -> f { _player = x })
enemy :: Lens' Board [Character]
enemy = lens _enemy (\f x -> f { _enemy = x })
turn :: Lens' Board Int
turn = lens _turn (\f x -> f { _turn = x })
tacticList :: Lens' Board TacticList
tacticList = lens _tacticList (\f x -> f { _tacticList = x })
battleState :: Lens' Board BattleState
battleState = lens _battleState (\f x -> f { _battleState = x })

attackCalc :: Character -> Int
attackCalc ch = (ch ^. strength) * 5

defenceCalc :: Character -> Int
defenceCalc ch = (ch ^. vitality) * 2

damageCalc :: Character -> Character -> Int
damageCalc s t = attackCalc s - defenceCalc t

toAction :: Target -> Command -> Action
toAction t Attack = AttackTo t
toAction t com = Iso com

runCommand :: Int -> StateT Board IO [Command]
runCommand tti = do
  tt <- use (tacticList . ixIM tti)
  forM (M.assocs tt) $ \(chara, cl) -> do
    let (com, cl') = getCommand cl
    tacticList . ixIM tti . ixM chara .= cl'
    return com

runBoard :: StateT Board IO ()
runBoard = do
  turn += 1

  comp <- runCommand 0
  pair1 <- liftM2 zip (return $ fmap (toAction ToEnemy) comp) (use player)

  es <- use enemy
  let (come, enemy') = unzip $ fmap (\e -> second (\cl -> e & commandList .~ cl) $ getCommand $ e^.commandList) es
  enemy .= enemy'
  pair2 <- liftM2 zip (return $ fmap (toAction ToPlayer) come) (use enemy)

  let ps = sortBy (\(_,a) (_,b) -> compare (a^.agility) (b^.agility)) $ concat [pair1,pair2]

  forM_ ps $ \(com,chara) -> case com of
    AttackTo ToPlayer -> do
      pchara <- use $ player . ix 0
      player . ix 0 . hp -= damageCalc chara pchara
    AttackTo ToEnemy -> do
      penemy <- use $ enemy . ix 0
      enemy . ix 0 . hp -= damageCalc chara penemy
    Iso _ -> return ()

  lift . print =<< use player
  lift . print =<< use enemy

  es <- use enemy
  when (all (\e -> e ^. hp <= 0) es) $ do
    battleState .= Win

  ps <- use player
  when (all (\p -> p ^. hp <= 0) ps) $ do
    battleState .= Lose

main = do
  let b = Board [princess, madman] [enemy1] 0 (IM.fromList []) Waiting
  execStateT (runBoard >> runBoard >> runBoard >> runBoard >> runBoard) b

{-
- STR: 攻撃ダメージ比率と攻撃ヒット率が上がる
- INT: 最大MPが上がる 回復スキルの回復量が上がる
- TEC: スキルダメージ比率が上がる 攻撃スキルの追加効果発生率が少し上がる
- VIT: 最大HPが上がる 防御力が上がる
- AGI: 速度補正率が上がる 回避率が少し上がる
- LUC: 確率スキルと装備品の成功率が上がる
-}
