import Init.Data.Array.Basic
import LeanReducers.Config
import LeanReducers.FoldSpec

namespace LeanReducers
namespace Internal

@[inline]
def foldRange (q : FoldSpec α ρ) (as : Array α) (start stop : Nat) : ρ :=
  as.foldr q.step q.unit (start := stop) (stop := start)

def foldArrayTaskCore (cfg : Config) (q : FoldSpec α ρ) (as : Array α)
    (start stop : Nat) : Nat → ρ
  | 0 => foldRange q as start stop
  | depth + 1 =>
      let len := stop - start
      if len ≤ cfg.grain then
        foldRange q as start stop
      else if len ≤ 1 then
        foldRange q as start stop
      else
        let mid := start + len / 2
        let right := Task.spawn (fun _ => foldArrayTaskCore cfg q as mid stop depth) cfg.priority
        let left := foldArrayTaskCore cfg q as start mid depth
        q.combine left right.get

def foldArrayTask (cfg : Config) (q : FoldSpec α ρ) (as : Array α) : Task ρ :=
  Task.spawn (fun _ => foldArrayTaskCore cfg q as 0 as.size cfg.maxDepth) cfg.priority

end Internal
end LeanReducers
