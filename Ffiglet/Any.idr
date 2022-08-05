module Ffiglet.Any

import Ffiglet.FFI

public export
record Any where
  constructor MkAny
  value : tpe

export
ToFFI Any AnyPtr where
  toFFI (MkAny v) = believe_me v

export
FromFFI Any AnyPtr where
  fromFFI = Just . MkAny

export
SafeCast Any where
  safeCast = Just . MkAny
