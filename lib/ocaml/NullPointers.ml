let magic = Obj.magic

module type NullSig = sig
   val null : 'a
   val is_null : 'a -> bool
end

module NullImpl : NullSig = struct
   let null = magic ()
   let is_null p = ((magic null) == p)
end

open NullImpl
let null = null
let is_null = is_null


let free x = ()
