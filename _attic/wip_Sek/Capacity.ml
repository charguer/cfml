let capacity = 32

let wrap_up n =
  if n >= capacity then n - capacity else n

let wrap_down n =
  if n < 0 then n + capacity else n
