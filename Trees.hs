{-# LANGUAGE FlexibleInstances, RecordWildCards, TupleSections, TypeSynonymInstances #-}
module Trees where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Array
import Data.Maybe ( catMaybes, fromJust, fromMaybe, isJust, isNothing )
import Data.List ( groupBy, intersperse, sortBy, unfoldr )
import Util.Display
import Util.Monad ( betweenM )
import Util.Prelude
import qualified Util.Unicode as U

data Tree a = Tree { left :: Maybe (Tree a),
                     value :: a,
                     right :: Maybe (Tree a)
                   }

data Coord a = Coord { x :: Integer,
                       y :: Integer,
                       val :: a
                     }               

instance Functor Tree where
  fmap f Tree{..} = Tree { left = fmap (fmap f) left,
                           value = f value,
                           right = fmap (fmap f) right
                         }

instance (Show a) => Show (Coord a) where
  show Coord{..} = "<" ++ (show x) ++ "," ++ (show y) ++ ">:" ++ (show val)

children :: Tree a -> [Tree a]
children Tree{..} = catMaybes [left,right]

height :: Tree a -> Integer
height Tree{..} = (max (maybe 0 height left) (maybe 0 height right)) + 1

tagWithLevels :: Tree a -> Tree (Integer, a)
tagWithLevels t = twl 0 t
  where twl n t@Tree{..} = t { left = fmap (twl $ n + 1) left,
                               value = (n, value),
                               right = fmap (twl $ n + 1) right }

levels :: Tree a -> [[a]]
levels t = let t' = tagWithLevels t
               nodes = inorder t'
               sameLevel n n' = fst n == fst n'
           in map (map snd) $ groupBy sameLevel nodes
  
preorder :: Tree a -> [a]
preorder Tree{..} = (value : maybe [] preorder left) ++ (maybe [] preorder right)

postorder :: Tree a -> [a]
postorder Tree{..} = (maybe [] postorder left) ++ (maybe [] postorder right) ++ (value : [])

inorder :: Tree a -> [a]
inorder Tree{..} = (maybe [] inorder left) ++ (value : []) ++ (maybe [] inorder right)

tree :: Tree a -> a -> Tree a -> Tree a
tree l v r = Tree { left = Just l, value = v, right = Just r }

treeL :: Tree a -> a -> Tree a
treeL l v = Tree { left = Just l, value = v, right = Nothing }

treeR :: a -> Tree a -> Tree a
treeR v r = Tree { left = Nothing, value = v, right = Just r }

leaf :: a -> Tree a
leaf v = Tree { left = Nothing, value = v, right = Nothing }

isLeaf :: Tree a -> Bool
isLeaf Tree{..} = isNothing left && isNothing right

isBranch :: Tree a -> Bool
isBranch Tree{..} = isJust left || isJust right 

trees :: [Tree Integer]
trees = [tree (tree (leaf 1) 2 (leaf 3)) 4 (tree (leaf 5) 6 (leaf 7)), -- ^ Perfect binary tree with Integer values
         treeL (treeR 2 (treeL (treeR 4 (treeL (treeR 6 (leaf 7) ) 5) ) 3) ) 1, -- ^ Maximally zig-zag tree (horrible under Knuth's algorithm)
         tree (tree (leaf 1) 2 (leaf 3)) 4 (leaf 5), -- ^ Not a perfect binary tree
         tree (tree (leaf 1) 2 (tree (leaf 3) 4 (leaf 5))) 6 (treeR 7 (treeR 8 (treeL (tree (tree (leaf 9) 10 (leaf 11)) 12 (leaf 13)) 14)))
        ]

trees' = tree (tree (leaf 'A') 'B' (leaf 'C')) 'D' (tree (leaf 'E') 'F' (leaf 'G')) -- ^ Perfect binary tree with Char values

type Layout a = Tree a -> CoordTree a

-- tr :: Layout a

-- | Each pair of Integers represents the leftmost and rightmost x-offsets of a node from the root (0) at a particular depth.
type LevelBounds = (Integer, Integer)
-- | A Contour is a list of levelBounds, starting from the root node, all the way down to the lowest leaf in the tree.
-- | The head of the list is the bounds of the level directly below the root.
type Contour = [LevelBounds]

-- | spacedTree takes a tree, and returns an annotated version of that same tree, where every node has a new value, a pair of the minimum separation distance between its subtrees and its old value
spacedTree :: Tree a -> Tree (a, Maybe Integer)
spacedTree t@Tree{..} = t { left = fmap spacedTree left,
                            value = (value, pure upToEven <*> minimumSubtreeSeparation t),
                            right = fmap spacedTree right
                          }
  where upToEven :: Integer -> Integer
        upToEven x = 2 * (ceiling $ (fromInteger x) / 2)

minimumSubtreeSeparation :: Tree a -> Maybe Integer
minimumSubtreeSeparation Tree{..} = pure minimumSeparationDistance <*> left <*> right

minimumSeparationDistance :: Tree a -> Tree a -> Integer
minimumSeparationDistance l r = maximum $ zipWith (\l r -> l - r + 1) innerEdgeL innerEdgeR
  where (innerEdgeL, innerEdgeR) = (map snd contourL, map fst contourR)
        (contourL, contourR) = (contour l, contour r)

overlappingSubtrees :: Tree a -> Tree a -> Bool
overlappingSubtrees l r = or $ zipWith (>=) innerEdgeL innerEdgeR
  where (innerEdgeL, innerEdgeR) = (map snd contourL, map fst contourR)
        (contourL, contourR) = (contour l, contour r)

contour :: Tree a -> Contour
contour t = unfoldr contour' [(t, 0)]

contour' :: [Offset a] -> Maybe (LevelBounds, [Offset a])
contour' [] = Nothing
contour' offsets = Just (fork minimum maximum $ map snd offsets, offsets')
  where offsets' = concatMap childrenOffsets offsets

        
type Offset a = (Tree a, Integer)

instance Show a => Show (Tree a) where
  show t = show $ value t
                        
childrenOffsets :: (Tree a, Integer) -> [(Tree a, Integer)]
childrenOffsets (Tree{..}, n) = map (\(a, b) -> (fromJust a, b)) $ filter (isJust . fst) [(left, n - 1), (right, n + 1)]

-- | Knuth's tree layout algorithm

type NextXDepth = State (Integer, Integer)

fmapM :: (a -> State c b) -> Maybe a -> State c (Maybe b)
fmapM f Nothing = return Nothing
fmapM f (Just x) = f x >>= (return . Just)

knuth :: Layout a
knuth t = evalState (knuth' t) (0, 0)
  where knuth' :: Tree a -> NextXDepth (CoordTree a)
        knuth' Tree{..} = do left' <- layoutSubtree left
                             cv <- coord value
                             right' <- layoutSubtree right
                             return $ Tree { left = left', value = cv, right = right' }
        layoutSubtree :: Maybe (Tree a) -> NextXDepth (Maybe (CoordTree a))
        layoutSubtree = fmapM (\subtree -> knuth' subtree `betweenM` (descend, ascend))
        coord :: a -> NextXDepth (Coord a)
        coord v = do (x', d) <- get
                     let c = Coord { x = x', y = d, val = v }
                     put (x' + 1, d)
                     return c

descend :: NextXDepth ()
descend = modify (\(x, d) -> (x, d + 1))

incrementX :: NextXDepth ()
incrementX = modify (\(x, d) -> (x + 1, d))

ascend :: NextXDepth ()
ascend = modify (\(x, d) -> (x, d - 1))

-- | Minimum Width tree layout
type NextPositions = State ([Integer], [Integer])

type CoordTree a = Tree (Coord a)

pop :: NextPositions Integer
pop = do ((x:xs), ys) <- get
         put (xs, x:ys)
         return x

push :: NextPositions ()
push = do (xs, ys) <- get
          put (case ys of
            [] -> (0 : xs, [])
            (y:ys') -> (y : xs, ys'))

getXAndIncrement :: NextPositions Integer
getXAndIncrement = do (x:xs, ys) <- get
                      put (x + 1 : xs, ys)
                      return x

getY :: NextPositions Integer
getY = gets ((subtract 1) . toInteger . length . fst)

minWidth :: Layout a
minWidth t = evalState (minWidth' t) ([0], [])
  where minWidth' :: Tree a -> NextPositions (CoordTree a)
        minWidth' Tree{..} = do left' <- layoutSubtree left
                                cv <- coord value
                                right' <- layoutSubtree right
                                return $ Tree { left = left', value = cv, right = right' }
        layoutSubtree :: Maybe (Tree a) -> NextPositions (Maybe (CoordTree a))
        layoutSubtree = fmapM (\subtree -> minWidth' subtree `betweenM` (push, pop))
        coord :: a -> NextPositions (Coord a)
        coord val' = do x' <- getXAndIncrement
                        y' <- getY
                        return $ Coord { x = x', y = y', val = val' }


instance (Show a) => Show (CoordTree a) where
  show t = show $ inorder t
                                
instance (Display a) => Display (CoordTree a) where
  display t = (concat . intersperse "\n" . map (concat . toPrintable)) $ rows t

rows :: CoordTree a -> [[Coord a]]
rows t = groupBy sameY $ sortBy (\a b -> y a `compare` y b) $ inorder t
  where sameY n n' = y n == y n'

toPrintable :: (Display a) => [Coord a] -> [String]
toPrintable row = map (maybe " " display) $ elems arr
  where arr = accumArray (flip const) Nothing (0, maximum $ map fst xs) xs
        xs = map (\Coord{x = x', val = val'} -> (x', Just val')) row        
