module Character (
  Command(..),
  Action(..),
  Target(..),
  CommandList(..),

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

  princess,
  sentry,
  madman,
  shaman,
  gambler,
  dancer,

  enemy1
) where

import qualified Data.IntMap as IM
import Lens.Family2
import Lens.Family2.State.Lazy
import Lens.Family2.Unchecked

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

-- princess = Character {
--   _name = "プリンセス",
--   _strength = 10,
--   _intelligence = 80,
--   _technique = 65,
--   _vitality = 40,
--   _agility = 50,
--   _luck = 20,
--   _level = 1,
--   _maxHP = 100,
--   _hp = 100,
--   _maxMP = 100,
--   _mp = 100,
--   _commandList = fromList []
-- }
--

princess = Character "プリンセス" 10 80 65 40 50 20 1 120 120 100 100 $ fromList []
sentry = Character "衛兵" 85 50 40 60 30 10 1 150 150 30 30 $ fromList []
madman = Character "狂人" 85 0 0 30 10 60 1 150 150 0 0 $ fromList []
shaman = Character "呪術師" 20 65 90 25 30 65 1 80 80 110 110 $ fromList []
gambler = Character "ギャンブラー" 30 45 30 55 60 85 1 100 100 140 140 $ fromList []
dancer = Character "踊り子" 65 30 35 55 75 80 1 100 100 70 70 $ fromList []

-- Character NAME STR INT TEC VIT AGI LUC LV HP MHP MP MMP

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
