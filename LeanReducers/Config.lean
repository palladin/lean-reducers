import Init.System.IO

namespace LeanReducers

/--
Runtime knobs for parallel reductions.

`grain` is the smallest chunk size worth splitting, `maxDepth` bounds the task
tree, and `priority` is passed to Lean's task scheduler.
-/
structure Config where
  grain : Nat := 2048
  maxDepth : Nat := 4
  priority : Task.Priority := Task.Priority.default
  deriving Repr

namespace Config

def default : Config := {}

end Config

end LeanReducers
