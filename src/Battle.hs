{-# LANGUAGE Rank2Types #-}
module Battle (
  ix,

  Character,
  name,
  strength,
  intelligence,
  technique,
  vitality,
  agility,
  luck,
  level,
  maxHP,
  hp,
  maxMP,
  mp,
  commandList,

  Board (Board),
  runBoard,
  player,
  enemy,

  princess,
  madman,
  sentry,
  enemy1
) where

import Control.Monad.State
import Data.List
import qualified Data.IntMap as IM
import Lens.Family2
import Lens.Family2.State.Lazy
import Lens.Family2.Unchecked

ix :: Int -> Lens' [a] a
ix n = lens (!! n) (\l x -> take (n-1) l ++ [x] ++ drop (n+1) l)

data Character = Character {
  _name :: String,
  _strength :: Int,
  _intelligence :: Int,
  _technique :: Int,
  _vitality :: Int,
  _agility :: Int,
  _luck :: Int,
  _level :: Int,
  _maxHP :: Int,
  _hp :: Int,
  _maxMP :: Int,
  _mp :: Int,
  _commandList :: CommandList
} deriving (Show)

name :: Lens' Character String
name = lens _name (\f x -> f { _name = x })
strength :: Lens' Character Int
strength = lens _strength (\f x -> f { _strength = x })
intelligence :: Lens' Character Int
intelligence = lens _intelligence (\f x -> f { _intelligence = x })
technique :: Lens' Character Int
technique = lens _technique (\f x -> f { _technique = x })
vitality :: Lens' Character Int
vitality = lens _vitality (\f x -> f { _vitality = x })
agility :: Lens' Character Int
agility = lens _agility (\f x -> f { _agility = x })
luck :: Lens' Character Int
luck = lens _luck (\f x -> f { _luck = x })
level :: Lens' Character Int
level = lens _level (\f x -> f { _level = x })
maxHP :: Lens' Character Int
maxHP = lens _maxHP (\f x -> f { _maxHP = x })
hp :: Lens' Character Int
hp = lens _hp (\f x -> f { _hp = x })
maxMP :: Lens' Character Int
maxMP = lens _maxMP (\f x -> f { _maxMP = x })
mp :: Lens' Character Int
mp = lens _mp (\f x -> f { _mp = x })
commandList :: Lens' Character CommandList
commandList = lens _commandList (\f x -> f { _commandList = x })

princess = Character {
  _name = "プリンセス",
  _strength = 10,
  _intelligence = 80,
  _technique = 65,
  _vitality = 40,
  _agility = 50,
  _luck = 20,
  _level = 1,
  _maxHP = 100,
  _hp = 100,
  _maxMP = 100,
  _mp = 100,
  _commandList = fromList [Attack, Defence, Attack]
}

sentry = Character {
  _name = "衛兵",
  _strength = 85,
  _intelligence = 50,
  _technique = 40,
  _vitality = 60,
  _agility = 30,
  _luck = 10,
  _level = 1,
  _maxHP = 150,
  _hp = 150,
  _maxMP = 30,
  _mp = 30,
  _commandList = fromList [Defence, Attack, Attack]
}

madman = Character {
  _name = "狂人",
  _strength = 85,
  _intelligence = 0,
  _technique = 0,
  _vitality = 30,
  _agility = 10,
  _luck = 60,
  _level = 1,
  _maxHP = 150,
  _hp = 150,
  _maxMP = 0,
  _mp = 0,
  _commandList = fromList [Attack, Attack, Defence]
}

enemy1 = Character {
  _name = "デビルエンペラー",
  _strength = 20,
  _intelligence = 20,
  _technique = 20,
  _vitality = 10,
  _agility = 40,
  _luck = 30,
  _level = 1,
  _maxHP = 5000,
  _hp = 5000,
  _maxMP = 40,
  _mp = 40,
  _commandList = fromList [Attack, Attack, Attack]
}

data Command = Attack | Defence | Escape deriving (Eq, Show)
data Action = AttackTo Target | Iso Command deriving (Show)
data Target = ToPlayer | ToEnemy deriving (Show)

data CommandList = CommandList {
  index :: Int,
  listSize :: Int,
  commandMap :: IM.IntMap Command
} deriving (Show)

fromList :: [Command] -> CommandList
fromList cs = CommandList 0 (length cs) (IM.fromList $ zip [0..] cs)

getCommand :: CommandList -> (Command, CommandList)
getCommand cl = (commandMap cl IM.! index cl, cl { index = nextIndex cl }) where
  nextIndex cl = if (index cl) == (listSize cl) - 1 then 0 else index cl + 1

runCharacter :: StateT Character IO Command
runCharacter = do
  comList <- use commandList
  let (c, cl) = getCommand comList
  commandList .= cl
  return c

data Board = Board {
  _player :: [Character],
  _enemy :: [Character],
  _turn :: Int
} deriving (Show)

player :: Lens' Board [Character]
player = lens _player (\f x -> f { _player = x })
enemy :: Lens' Board [Character]
enemy = lens _enemy (\f x -> f { _enemy = x })
turn :: Lens' Board Int
turn = lens _turn (\f x -> f { _turn = x })

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
  let b = Board [princess, madman] [enemy1] 0
  execStateT (runBoard >> runBoard >> runBoard >> runBoard >> runBoard) b

{-
- STR: 攻撃ダメージ比率と攻撃ヒット率が上がる
- INT: 最大MPが上がる 回復スキルの回復量が上がる
- TEC: スキルダメージ比率が上がる 攻撃スキルの追加効果発生率が少し上がる
- VIT: 最大HPが上がる 防御力が上がる
- AGI: 速度補正率が上がる 回避率が少し上がる
- LUC: 確率スキルと装備品の成功率が上がる
-}
