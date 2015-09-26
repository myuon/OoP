module Character (
  Command(..),
  Action(..),
  Target(..),
  CommandList(..),
  fromList,

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

  enemy1,

  characterDetailHTML
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

instance Eq Character where
  c1 == c2 = (c1 ^. name) == (c2 ^. name)

princess = Character "プリンセス" 10 80 65 40 50 20 1 60 60 50 50 $ fromList []
sentry = Character "衛兵" 85 50 40 60 30 10 1 80 80 20 20 $ fromList []
madman = Character "狂人" 85 0 0 30 10 60 1 80 80 0 0 $ fromList []
shaman = Character "呪術師" 20 65 90 25 30 65 1 40 40 80 80 $ fromList []
gambler = Character "ギャンブラー" 30 45 30 55 60 85 1 50 50 70 70 $ fromList []
dancer = Character "踊り子" 65 30 35 55 75 80 1 55 55 65 65 $ fromList []

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

characterDetailHTML :: Character -> String
characterDetailHTML c = concat $
  ["<div class=\"col-md-4 career\" id=\"character-detail-" ++ c ^. name ++ "\">",
  "<div class=\"panel panel-default\">",
  "  <div class=\"panel-heading\">",
  "    <h3 class=\"panel-title\">",
  "      " ++ c^.name ++ "(<a data-toggle=\"modal\" data-target=\"#myModal\"> S </a> )",
  "    </h3>",
  "  </div>",
  "  <div class=\"panel-body\">"]
  ++ listParameterHTML ++
  ["    <p>",
  "      <strong>固有スキル</strong><br>",
  "      特殊陣営・デッキ拡張・王の力",
  "    </p>",
  "    <div id=\"join-party-btn\"></div>",
--  "    <button type=\"button\" class=\"btn btn-primary\">パーティに入れる</button>",
  "  </div>",
  "</div>",
  "</div>",
  "</div>"]
  where
    listParameterHTML :: [String]
    listParameterHTML = map (uncurry parameterHTML) $
      zip ["STR","INT","TEC","VIT","AGI","LUC","LV","HP","MP"]
          [c^.strength, c^.intelligence, c^.technique, c^.vitality, c^.agility, c^.luck, c^.level, c^.maxHP, c^.maxMP]

    parameterHTML p v = concat $ [
      "<div class=\"row\">",
      "  <div class=\"col-md-3\">" ++ p ++ "</div>",
      "  <div class=\"col-md-8\">",
      "    <div class=\"progress\">",
      "      <div class=\"progress-bar\" role=\"progressbar\" style=\"width: " ++ show v ++ "%;\"></div>",
      "    </div>",
      "  </div>",
      "</div>"]
