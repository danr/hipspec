
-- Turns
--
-- f :: C a => ... a ...
--
-- into
--
-- f :: ... D ...
--
-- where D is a type that could be specified as a parameter, but is just
-- Int for now.
--
-- Blech, while this could work, the properties are still expressed with
-- dictionaries everywhere

module HipSpec.GHC.Unclassifier where

unclassify :: [(Var,CoreExpr)]


