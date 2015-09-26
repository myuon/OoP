{-# LANGUAGE Rank2Types #-}
module Battle (
  ix,

  Board (Board),
  Tactic,
  TacticList,
  addTactic,
  runBoard,
  player,
  enemy,
  turn,
  tacticList,

  module Character
) where

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

getCommand :: CommandList -> (Command, CommandList)
getCommand cl = (commandMap cl IM.! index cl, cl { index = nextIndex cl }) where
  nextIndex cl = if (index cl) == (listSize cl) - 1 then 0 else index cl + 1

runCharacter :: StateT Character IO Command
runCharacter = do
  comList <- use commandList
  let (c, cl) = getCommand comList
  commandList .= cl
  return c

type Tactic = M.Map String CommandList
type TacticList = IM.IntMap Tactic

addTactic :: Tactic -> TacticList -> TacticList
addTactic x tt = IM.insert (mi + 1) x tt where
  mi = maximum $ IM.keys tt

data Board = Board {
  _player :: [Character],
  _enemy :: [Character],
  _turn :: Int,
  _tacticList :: TacticList
} deriving (Show)

player :: Lens' Board [Character]
player = lens _player (\f x -> f { _player = x })
enemy :: Lens' Board [Character]
enemy = lens _enemy (\f x -> f { _enemy = x })
turn :: Lens' Board Int
turn = lens _turn (\f x -> f { _turn = x })
tacticList :: Lens' Board TacticList
tacticList = lens _tacticList (\f x -> f { _tacticList = x })

attackCalc :: Character -> Int
attackCalc ch = (ch ^. strength) * 5

defenceCalc :: Character -> Int
defenceCalc ch = (ch ^. vitality) * 2

damageCalc :: Character -> Character -> Int
damageCalc s t = attackCalc s - defenceCalc t

toAction :: Target -> Command -> Action
toAction t Attack = AttackTo t
toAction t com = Iso com

runBoard :: StateT Board IO ()
runBoard = do
  turn += 1

  (comp, player') <- lift . fmap unzip . mapM (runStateT runCharacter) =<< use player
  player .= player'
  pair1 <- liftM2 zip (return (fmap (toAction ToEnemy) comp)) (use player)

  (come, enemy') <- lift . fmap unzip . mapM (runStateT runCharacter) =<< use enemy
  enemy .= enemy'
  pair2 <- liftM2 zip (return (fmap (toAction ToPlayer) comp)) (use enemy)

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

main = do
  let b = Board [princess, madman] [enemy1] 0 $ IM.fromList []
  execStateT (runBoard >> runBoard >> runBoard >> runBoard >> runBoard) b

{-
- STR: 攻撃ダメージ比率と攻撃ヒット率が上がる
- INT: 最大MPが上がる 回復スキルの回復量が上がる
- TEC: スキルダメージ比率が上がる 攻撃スキルの追加効果発生率が少し上がる
- VIT: 最大HPが上がる 防御力が上がる
- AGI: 速度補正率が上がる 回避率が少し上がる
- LUC: 確率スキルと装備品の成功率が上がる
-}
