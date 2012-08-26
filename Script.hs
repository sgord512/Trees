import Trees

import Data.Maybe ( fromJust )

import Util.Display

t = head trees
l = fromJust $ left t
r = fromJust $ right t

st = spacedTree t
