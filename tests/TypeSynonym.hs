module TypeSynonym where

type Boolean = Bool

(&&&) :: Boolean -> Boolean -> Boolean
True  &&& a = a
False &&& _ = False
