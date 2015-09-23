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

data Field = Field {
  _keyStates :: IM.IntMap Bool,
  _position :: (Int,Int),
  _positionPrev :: (Int,Int),
  _dMap :: DMap,
  _dDiscoverMap :: DMap
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

dWidth = 30
dHeight = 30

defField :: IO Field
defField = do
  dm <- buildDungeon
  p <- chooseSpawn dm

  return $ Field {
    _keyStates = IM.fromList [(i,False) | i<-[0..255]],
    _position = p,
    _positionPrev = p,
    _dMap = dm,
    _dDiscoverMap = areaWith '.'
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

getParent :: Elem -> IO Elem
getParent= ffi $ toJSString "(function(e){return e.parentNode;})"

main = do
  reff <- newIORef =<< defField
  field <- readIORef reff

  onEvent document KeyPress $ \key -> do
    let n = keyCode key
    modifyIORef reff (keyStates %~ IM.insert n True)

    withElem "dungeon-field" $ \e -> do
      pe <- getParent e
      pe `hasClass` "active" >>= \a -> when a $ do
        onceStateT reff updateField

  onEvent document KeyUp $ \key -> do
    let n = keyCode key
    modifyIORef reff (keyStates %~ IM.insert n False)

  onceStateT reff updateField
  -- field <- readIORef reff
  -- withElem "dungeon-field" $ \e ->
  --   setProp e "innerHTML" $ htmlDMap $ field ^. dDiscoverMap

updateField :: StateT Field IO ()
updateField = do
  p <- use position
  positionPrev .= p

  keys <- use keyStates
  when (keys IM.! 38) $ do
    position %= (\(x,y) -> (x,y-1))
  when (keys IM.! 40) $ do
    position %= (\(x,y) -> (x,y+1))
  when (keys IM.! 37) $ do
    position %= (\(x,y) -> (x-1,y))
  when (keys IM.! 39) $ do
    position %= (\(x,y) -> (x+1,y))

  dm <- use dMap
  (px,py) <- use position
  dDiscoverMap %= insertAll (fmap (\i -> (i, dm M.! i))
    [(px+dx,py+dy) | [dx,dy] <- replicateM 2 [-1,0,1],
        0 <= px+dx && px+dx <= width - 1,
        0 <= py+dy && py+dy <= height - 1])

  pos <- use position
  Just pl <- elemById "player"
  setProp pl "innerHTML" $ concat $ replicate (snd pos) "<br>" ++ replicate (fst pos) "&nbsp;" ++ ["@"]

  -- return pl `with` [
  --   style "left" =: ((show $ 10 * fst pos) ++ "px"),
  --   style "top" =: ((show $ 12 * snd pos) ++ "px")]

  ddm <- use dDiscoverMap
  withElem "dungeon-field" $ \e ->
    setProp e "innerHTML" $ htmlDMap $ ddm

onceStateT :: IORef s -> StateT s IO () -> IO ()
onceStateT ref m = do
  x <- readIORef ref
  x' <- execStateT m x
  writeIORef ref $! x'

loopStateT :: Int -> IORef s -> StateT s IO () -> IO ()
loopStateT c ref m = void $ setTimer (Repeat c) $ onceStateT ref m
