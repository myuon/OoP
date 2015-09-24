module Main where

import Haste
import Haste.DOM hiding (set)
import Haste.Events
import Haste.Foreign
import Haste.Graphics.Canvas
import Control.Monad
import Control.Monad.State
import Data.IORef
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.List
import Lens.Family2
import Lens.Family2.State.Lazy
import Lens.Family2.Unchecked

import Dungeon
import Battle

data Screen = Default | Battle deriving (Show)
data Field = Field {
  _keyStates :: IM.IntMap Bool,
  _position :: (Int,Int),
  _positionPrev :: (Int,Int),
  _dMap :: DMap,
  _dDiscoverMap :: DMap,
  _encounterCount :: Int,
  _screen :: Screen,
  _board :: Board
} deriving (Show)

keyStates :: Lens' Field (IM.IntMap Bool)
keyStates = lens _keyStates (\f x -> f { _keyStates = x })
position :: Lens' Field (Int,Int)
position = lens _position (\f x -> f { _position = x })
positionPrev :: Lens' Field (Int,Int)
positionPrev = lens _positionPrev (\f x -> f { _positionPrev = x })
dMap :: Lens' Field DMap
dMap = lens _dMap (\f x -> f { _dMap = x })
dDiscoverMap :: Lens' Field DMap
dDiscoverMap = lens _dDiscoverMap (\f x -> f { _dDiscoverMap = x })
encounterCount :: Lens' Field Int
encounterCount = lens _encounterCount (\f x -> f { _encounterCount = x })
board :: Lens' Field Board
board = lens _board (\f x -> f { _board = x })

dWidth = 45
dHeight = 35

defField :: IO Field
defField = do
  dm <- buildDungeon
  p <- chooseSpawn dm

  return $ Field {
    _keyStates = IM.fromList [(i,False) | i<-[0..255]],
    _position = p,
    _positionPrev = p,
    _dMap = dm,
    _dDiscoverMap = areaWith '.',
    _encounterCount = 0,
    _screen = Default,
    _board = Board [princess,madman,sentry] [enemy1] 0
  }

htmlDMap :: DMap -> String
htmlDMap k = concat $ fmap escapeChar $ unbrs $ fmap (take dWidth . showLine) [0..(height - 1) `min` dHeight] where
  showLine :: Int -> String
  showLine j = fmap (k M.!) [(i,j) | i<-[0..width - 1]]

  unbrs :: [String] -> String
  unbrs xs = intercalate "<br>" xs

  escapeChar :: Char -> String
  escapeChar ' ' = "&nbsp;"
  escapeChar x = return x

getParent :: MonadIO m => Elem -> m Elem
getParent= liftIO . f where
  f :: Elem -> IO Elem
  f = ffi $ toJSString "(function(e){return e.parentNode;})"

setHTML :: MonadIO m => Elem -> String -> m ()
setHTML el t = setProp el "innerHTML" t

appendHTML :: MonadIO m => Elem -> String -> m ()
appendHTML el t = do
  s <- getProp el "innerHTML"
  setProp el "innerHTML" $ s ++ t

main = do
  reff <- newIORef =<< defField
  field <- readIORef reff

  onEvent document KeyPress $ \key -> do
    let n = keyCode key
    modifyIORef reff (keyStates %~ IM.insert n True)

    withElem "dungeon-field" $ \e -> do
      pe <- getParent =<< getParent e
      pe `hasClass` "active" >>= \a -> when a $ do
        onceStateT reff $ updateField reff

  onEvent document KeyUp $ \key -> do
    let n = keyCode key
    modifyIORef reff (keyStates %~ IM.insert n False)

  onceStateT reff $ updateField reff

  withElem "battle" $ \e ->
    initBattleScreen e reff

characterPlayerHTML :: Character -> String
characterPlayerHTML chara = concat [
  "<div class=\"col-md-4\">",
  "  <div class=\"player\">",
  "    <span id=\"player-display-name\"></span><br>",
  "    HP <span id=\"player-display-hp\"></span> / <span id=\"player-display-maxhp\"></span>",
  "    <div class=\"progress\">",
  "      <div class=\"progress-bar\" role=\"progressbar\" id=\"player-display-hpratio\">",
  "      </div>",
  "    </div>",
  "    MP <span id=\"player-display-mp\"></span> / <span id=\"player-display-maxmp\"></span>",
  "    <div class=\"progress\">",
  "      <div class=\"progress-bar progress-bar-info\" role=\"progressbar\" id=\"player-display-mpratio\">",
  "      </div>",
  "    </div>",
  "  </div>",
  "</div>"
  ]

characterEnemyHTML :: Character -> String
characterEnemyHTML chara = concat [
  "<div class=\"col-md-4\">",
  "  <div class=\"enemy\">",
  "    <span id=\"enemy-display-name\"></span><br>",
  "    HP",
  "    <div class=\"progress\">",
  "      <div class=\"progress-bar\" role=\"progressbar\" id=\"enemy-display-hpratio\">",
  "      </div>",
  "    </div>",
  "  </div>",
  "</div>"
  ]

initBattleScreen :: MonadIO m => Elem -> IORef Field -> m ()
initBattleScreen em reff = do
  b <- liftIO $ fmap (^. board) $ readIORef reff

  withElemsQS em "#player-chara" $ \[e] -> do
    forM_ (b ^. player) $ \p -> do
      appendHTML e $ characterPlayerHTML p

  withElemsQS em "#enemy-chara" $ \[e] -> do
    forM_ (b ^. enemy) $ \p -> do
      appendHTML e $ characterEnemyHTML p

  displayBattleScreen em b

  withElemsQS em "#step-battle" $ \[e] -> do
    liftIO $ onEvent e Click $ \_ -> do
      onceStateT reff $ zoom board runBoard

      b <- fmap (^. board) $ readIORef reff
      displayBattleScreen em b

  return ()

displayBattleScreen :: MonadIO m => Elem -> Board -> m ()
displayBattleScreen em b = do
  withElemsQS em "#player-chara" $ mapM_ $ \e0 -> do
    let insertText eid s = do {
      withElemsQS e0 eid $ \es -> do
        forM_ (zip es $ b ^. player) $ \(e,p) -> do
          setHTML e (s p)
    }

    insertText "#player-display-name" $ \p -> p ^. name
    insertText "#player-display-hp" $ \p -> show $ p ^. hp
    insertText "#player-display-maxhp" $ \p -> show $ p ^. maxHP

    withElemsQS e0 "#player-display-hpratio" $ \es -> do
      forM_ (zip es $ b ^. player) $ \(e,p) -> do
        setStyle e "width" $ (++ "%") $ show $ (p ^. hp) * 100 `div` (p ^. maxHP)

    insertText "#player-display-mp" $ \p -> show $ p ^. mp
    insertText "#player-display-maxmp" $ \p -> show $ p ^. maxMP

    withElemsQS e0 "#player-display-mpratio" $ \es -> do
      forM_ (zip es $ b ^. player) $ \(e,p) -> do
        when (p ^. maxMP /= 0) $ do
          setStyle e "width" $ (++ "%") $ show $ (p ^. mp) * 100 `div` (p ^. maxMP)

  withElemsQS em "#enemy-chara" $ mapM_ $ \e0 -> do
    let insertText eid s = do {
      withElemsQS e0 eid $ \es -> do
        forM_ (zip es $ b ^. enemy) $ \(e,p) -> do
          setHTML e (s p)
    }

    insertText "#enemy-display-name" $ \p -> p ^. name

    withElemsQS e0 "#enemy-display-hpratio" $ \es -> do
      forM_ (zip es $ b ^. enemy) $ \(e,p) -> do
        setStyle e "width" $ (++ "%") $ show $ (p ^. hp) * 100 `div` (p ^. maxHP)

notBlock :: (Int,Int) -> StateT Field IO Bool
notBlock p = do
  dm <- use dMap
  return $ dm M.! p == '#' || dm M.! p == '-'

updateField :: IORef Field -> StateT Field IO ()
updateField reff = do
  p <- use position
  positionPrev .= p

  keys <- use keyStates
  when (keys IM.! 38) $ moveTo (0,-1)
  when (keys IM.! 40) $ moveTo (0,1)
  when (keys IM.! 37) $ moveTo (-1,0)
  when (keys IM.! 39) $ moveTo (1,0)

  dm <- use dMap
  (px,py) <- use position
  dDiscoverMap %= insertAll (fmap (\i -> (i, dm M.! i))
    [(px+dx,py+dy) | [dx,dy] <- replicateM 2 [-2,-1,0,1,2],
        0 <= px+dx && px+dx <= width - 1,
        0 <= py+dy && py+dy <= height - 1])

  pos <- use position
  Just pl <- elemById "player"
  setProp pl "innerHTML" $ concat $ replicate (snd pos) "<br>" ++ replicate (fst pos) "&nbsp;" ++ ["@"]

  ddm <- use dDiscoverMap
  withElem "dungeon-field" $ \e ->
    setProp e "innerHTML" $ htmlDMap $ ddm

  ec <- use encounterCount
  when (ec == 5) $ do
    encounterCount .= 0
    lift $ tabon ()

    withElemsQS document "#tabs a[href=\"#dungeon-battle\"]" $ \[e] -> do
      e' <- getParent e
      setStyle e' "display" "block"

    withElem "dungeon-battle" $ \e -> do
      initBattleScreen e reff

  where
    tabon :: () -> IO ()
    tabon = ffi $ toJSString "function(){ $('#tabs a[href=\"#dungeon-battle\"]').tab('show'); }"

    moveTo (dx,dy) = do
      (x,y) <- use position
      let p' = (x+dx,y+dy)
      t <- notBlock p'
      when t $ do
        position .= p'
        encounterCount += 1

onceStateT :: IORef s -> StateT s IO () -> IO ()
onceStateT ref m = do
  x <- readIORef ref
  x' <- execStateT m x
  writeIORef ref $! x'

loopStateT :: Int -> IORef s -> StateT s IO () -> IO ()
loopStateT c ref m = void $ setTimer (Repeat c) $ onceStateT ref m
