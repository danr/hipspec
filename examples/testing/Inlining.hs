module Inlining where

import HipSpec.Prelude

prop_and x y = x && y =:= y && x

