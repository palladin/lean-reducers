import Init.System.IO

namespace LeanReducers

/-- Ordered, bounded IO tasks. Drain every started task before throwing the
first error in input order, so scoped resources can be released safely.
Later batches are not started after an error. -/
def mapTasks (concurrency : Nat) (values : Array α) (f : α → IO β) : IO (Array β) := do
  let width := max 1 concurrency
  let mut result := #[]
  for batch in [:((values.size + width - 1) / width)] do
    let mut tasks := #[]
    let mut launchError : Option IO.Error := none
    for value in values.extract (batch * width) ((batch + 1) * width) do
      try tasks := tasks.push (← IO.asTask (f value))
      catch error => launchError := some error; break
    let outcomes ← tasks.mapM fun task => (IO.wait task : IO _)
    for outcome in outcomes do result := result.push (← IO.ofExcept outcome)
    if let some error := launchError then throw error
  return result

end LeanReducers
