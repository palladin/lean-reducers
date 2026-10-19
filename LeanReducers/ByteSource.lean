import Init.System.IO

namespace LeanReducers

/-- Immutable, seekable bytes. `read offset count` must return exactly
`min count (size - offset)` bytes, or throw. Reads may run concurrently.
Adapters own authentication, integrity checking and bounded caching. -/
structure ByteSource where
  size : Nat
  read : Nat → Nat → IO ByteArray
  name : String := "byte source"

/-- A half-open byte interval. Adjacent intervals may cut through UTF-8 or a
line; the line producer repairs both boundaries when it reads them. The source
can be a local reader or a serializable descriptor used by a distributed caller. -/
structure ByteRange (σ : Type) where
  source : σ
  start : Nat
  stop : Nat
  deriving Repr, BEq

namespace ByteRange

def size (range : ByteRange σ) : Nat := range.stop - range.start

def map (f : σ → τ) (range : ByteRange σ) : ByteRange τ :=
  { source := f range.source, start := range.start, stop := range.stop }

/-- Split without reading any data. Keep empty sources once, and preserve order. -/
def partition (ranges : Array (ByteRange σ)) (bytes : Nat) : Array (ByteRange σ) := Id.run do
  let bytes := max 1 bytes
  let mut result := #[]
  for range in ranges do
    for i in [:max 1 ((range.size + bytes - 1) / bytes)] do
      result := result.push { range with
        start := range.start + i * bytes, stop := min range.stop (range.start + (i + 1) * bytes) }
  return result

/-- Balance a task tree by bytes, splitting even a single large source. -/
def splitAtHalf (ranges : Array (ByteRange σ)) :
    Option (Array (ByteRange σ) × Array (ByteRange σ)) := Id.run do
  let total := ranges.foldl (fun n range => n + range.size) 0
  let target := total / 2
  let mut left := #[]
  let mut right := #[]
  let mut used := 0
  for range in ranges do
    if used ≥ target then right := right.push range
    else if used + range.size ≤ target then
      left := left.push range
      used := used + range.size
    else
      let cut := range.start + target - used
      left := left.push { range with stop := cut }
      right := right.push { range with start := cut }
      used := target
  if left.isEmpty || right.isEmpty then
    let mid := ranges.size / 2
    if mid == 0 then return none
    return some (ranges.extract 0 mid, ranges.extract mid ranges.size)
  return some (left, right)

end ByteRange
end LeanReducers
