--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/19/19                --
--------------------------------------------

module Interactive
  (
    Definition(..)
  , State(..)
  , LineType(..)

  ) where


-- Domestic Imports
import Primitives ( Term(..), Type(..), Definition(..) )


-- | The State datum represents the state of the interpreter. The first
-- element of the tuple is the list of loaded filenames, the second is
-- the list of definitions, and the last is the prelude (the actual text
-- from the files)
type State = ([String], [Definition], String)

-- | The LineType datum represents a kind of input line.
data LineType = 
    Input String 
  | Command String [String]
  | Null
  | Exit