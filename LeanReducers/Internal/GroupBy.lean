import Init.Data.Array.Basic
import LeanReducers.Algebra

namespace LeanReducers
namespace Internal

def removeGroupKey [BEq κ] (k : κ) (groups : Array (κ × ν)) : Array (κ × ν) :=
  groups.foldl (fun acc row => if row.1 == k then acc else acc.push row) #[]

def groupStep [BEq κ] (valueSpec : MonoidSpec ν) (key : α → κ) (step : α → ν → ν)
    (a : α) (groups : Array (κ × ν)) : Array (κ × ν) :=
  let k := key a
  match groups.find? (fun row => row.1 == k) with
  | some row => #[(k, step a row.2)] ++ removeGroupKey k groups
  | none => #[(k, step a valueSpec.unit)] ++ groups

def mergeGroupInto [BEq κ] (valueSpec : MonoidSpec ν)
    (groups : Array (κ × ν)) (row : κ × ν) : Array (κ × ν) :=
  match groups.findIdx? (fun existing => existing.1 == row.1) with
  | some i => groups.modify i (fun existing => (existing.1, valueSpec.combine existing.2 row.2))
  | none => groups.push row

def mergeGroups [BEq κ] (valueSpec : MonoidSpec ν)
    (left right : Array (κ × ν)) : Array (κ × ν) :=
  right.foldl (mergeGroupInto valueSpec) left

end Internal
end LeanReducers
