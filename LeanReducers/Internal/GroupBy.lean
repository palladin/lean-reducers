import Std.Data.HashMap.Basic
import LeanReducers.Algebra

namespace LeanReducers
namespace Internal

abbrev Groups (κ ν : Type) [BEq κ] [Hashable κ] :=
  Std.HashMap κ ν

def emptyGroups [BEq κ] [Hashable κ] : Groups κ ν :=
  {}

def groupsToArray [BEq κ] [Hashable κ] (groups : Groups κ ν) : Array (κ × ν) :=
  groups.toArray

def groupStep [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν) (key : α → κ)
    (step : α → ν → ν) (a : α) (groups : Groups κ ν) : Groups κ ν :=
  let k := key a
  groups.insert k (step a (groups.getD k valueSpec.unit))

def mergeGroupInto [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν)
    (groups : Groups κ ν) (k : κ) (v : ν) : Groups κ ν :=
  let value :=
    match groups.get? k with
    | some existing => valueSpec.combine existing v
    | none => v
  groups.insert k value

def mergeGroups [BEq κ] [Hashable κ] (valueSpec : MonoidSpec ν)
    (left right : Groups κ ν) : Groups κ ν :=
  right.fold (mergeGroupInto valueSpec) left

end Internal
end LeanReducers
