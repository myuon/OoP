module Dungeon (width, height, area, areaWith, DMap, insertAll, buildDungeon, chooseSpawn) where

--import System.Random
import Haste
import qualified Data.Map as M
import Data.List
import Control.Monad.State
import Debug.Trace

randomRIO :: (Random a) => (a,a) -> IO a
randomRIO ix = do
  sd <- newSeed
  return $ fst $ randomR ix sd

type DMap = M.Map (Int,Int) Char

width = 45
height = 35
complexity = 2

area :: DMap
area = areaWith ' '

areaWith :: Char -> DMap
areaWith c = M.fromList $ zip [(i,j) | i<-[0..width - 1], j<-[0..height - 1]] $ repeat c

roomMinWidth = 2
roomMinHeight = 2

type Box = ((Int,Int),(Int,Int))
type Block = [Box]

chunksOf :: Int -> [a] -> [[a]]
chunksOf n [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)

sortFst :: (Ord a) => [(a,b)] -> [(a,b)]
sortFst = sortBy (\a b -> compare (fst a) (fst b))

sortSnd :: (Ord b) => [(a,b)] -> [(a,b)]
sortSnd = sortBy (\a b -> compare (snd a) (snd b))

splitMapDown :: Block -> IO Block
splitMapDown bs = fmap concat $ mapM split bs where
  split ((x1,y1),(x2,y2)) = do
    x <- randomRIO (x1 + roomMinWidth + 1, x2 - roomMinWidth - 1)
    if x2 - x1 >= roomMinWidth + 2
      then return $ [((x1,y1), (x,y2)), ((x,y1), (x2,y2))]
      else return []

splitMapAcross :: Block -> IO Block
splitMapAcross bs = fmap concat $ mapM split bs where
  split ((x1,y1),(x2,y2)) = do
    y <- randomRIO (y1 + roomMinHeight + 1, y2 - roomMinHeight - 1)
    if y2 - y1 >= roomMinHeight + 2
      then return $ [((x1,y1), (x2,y)), ((x1,y), (x2,y2))]
      else return []

iterateSplit :: Block -> Int -> IO Block
iterateSplit bs n = foldr (\_ m -> m >>= splitMapDown >>= splitMapAcross) (return bs) [0..n - 1]

insertAll :: Ord k => [(k,a)] -> M.Map k a -> M.Map k a
insertAll ks m = foldr (\(k,x) -> M.insert k x) m ks

boxList :: (Int,Int) -> (Int,Int) -> a -> [((Int,Int),a)]
boxList (x1,y1) (x2,y2) a = zip [(i,j) | i<-[x1..x2], j<-[y1..y2]] $ repeat a

arrangeRooms :: Block -> IO Block
arrangeRooms bs = foldr (\x m -> liftM2 (++) (build x) m) (return []) bs where
  build ((x1,y1),(x2,y2)) = do
    x <- randomRIO (x1 + 1, x2 - roomMinWidth)
    x' <- randomRIO (x + roomMinWidth - 1, x2 - 1)
    y <- randomRIO (y1 + 1, y2 - roomMinHeight)
    y' <- randomRIO (y + roomMinHeight - 1, y2 - 1)
    if x1 + 1 <= x2 - roomMinWidth && y1 + 1 <= y2 - roomMinHeight
      then return [((x,y),(x',y'))]
      else return []

paintBoxWith :: Char -> Block -> DMap -> DMap
paintBoxWith c bs m = foldr (\(p1,p2) -> insertAll (boxList p1 p2 c)) m bs

paintDotWith :: Char -> [(Int,Int)] -> DMap -> DMap
paintDotWith c bs m = foldr (\p -> M.insert p c) m bs

buildCorridor :: Block -> Block -> IO (Block, [(Int,Int)])
buildCorridor bs ws = do
  c1 <- fmap concat $ mapM (\(b,w) -> buildTop b w) $ zip bs ws
  c2 <- fmap concat $ mapM (\(b,w) -> buildBottom b w) $ zip bs ws
  c3 <- fmap concat $ mapM (\(b,w) -> buildLeft b w) $ zip bs ws
  c4 <- fmap concat $ mapM (\(b,w) -> buildRight b w) $ zip bs ws
  let cs = concat [c1,c2,c3,c4]
  return $ (fmap fst cs, fmap snd cs)
  where
    buildTop ((bx1,by1),(bx2,by2)) ((x1,y1),(x2,y2)) = do
      if by1 /= 0
        then do
          x <- randomRIO (x1,x2)
          return $ [(((x,by1),(x,y1)), (x,by1))]
        else return []
    buildBottom ((bx1,by1),(bx2,by2)) ((x1,y1),(x2,y2)) = do
      if by2 /= height - 1
        then do
          x <- randomRIO (x1,x2)
          return $ [(((x,y2),(x,by2)), (x,by2))]
        else return []
    buildLeft ((bx1,by1),(bx2,by2)) ((x1,y1),(x2,y2)) = do
      if bx1 /= 0
        then do
          y <- randomRIO (y1,y2)
          return $ [(((bx1,y),(x1,y)), (bx1,y))]
        else return []
    buildRight ((bx1,by1),(bx2,by2)) ((x1,y1),(x2,y2)) = do
      if bx2 /= width - 1
        then do
          y <- randomRIO (y1,y2)
          return $ [(((x2,y),(bx2,y)), (bx2,y))]
        else return []

buildBridge :: Block -> [(Int,Int)] -> IO Block
buildBridge bs ps = do
  let pairDown = concat $ fmap (chunksOf 2 . sortFst) $ groupBy (\a b -> snd a == snd b) $ sortSnd $ fmap getEdge $ pickDown
  let pairAcross = concat $ fmap (chunksOf 2 . sortSnd) $ groupBy (\a b -> fst a == fst b) $ sortFst $ fmap getEdge $ pickAcross

  return $ fmap tup $ concat $ [pairDown, pairAcross]

  where
    tup [x] = (x,x)
    tup [a,b] = (a,b)

    pickDown = filter (\((x1,y1),(x2,y2)) -> x1 == x2) bs
    pickAcross = filter (\((x1,y1),(x2,y2)) -> y1 == y2) bs

    getEdge ((x1,y1),(x2,y2))
      | (x1,y1) `elem` ps = (x1,y1)
      | otherwise = (x2,y2)

buildDoor :: Block -> [(Int,Int)] -> [(Int,Int)]
buildDoor bs ps = fmap getNonEdge bs where
  getNonEdge ((x1,y1),(x2,y2))
    | (x1,y1) `elem` ps = (x2,y2)
    | otherwise = (x1,y1)

showDMap :: DMap -> String
showDMap k = unlines $ fmap showLine [0..height - 1] where
  showLine j = fmap (k M.!) [(i,j) | i<-[0..width - 1]]

buildDungeon :: IO DMap
buildDungeon = do
  bs <- iterateSplit [((0,0),(width-1,height-1))] complexity
  ws <- arrangeRooms bs
  (cor,es) <- buildCorridor bs ws
  bdg <- buildBridge cor es
  return $ paintDotWith '#' (buildDoor cor es) $ paintBoxWith '#' ws $ paintBoxWith '-' cor $ paintBoxWith '-' bdg $ area

choose :: (Show a) => [a] -> IO a
choose xs = do
  n <- randomRIO (0, length xs - 1)
  return $ xs !! n

chooseSpawn :: DMap -> IO (Int,Int)
chooseSpawn dm = choose $
  [(i,j) | i<-[0..20], j<-[0..20], dm M.! (i,j) == '#']

main = do
  putStrLn . showDMap =<< buildDungeon
