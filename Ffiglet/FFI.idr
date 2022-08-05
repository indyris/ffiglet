module Ffiglet.FFI

public export
interface SafeCast a where
  safeCast : {0 x : Type} -> x -> Maybe a

public export
interface ToFFI a ffiRepr | a where
  toFFI : a -> ffiRepr

export
ToFFI AnyPtr AnyPtr where toFFI = id

export
ToFFI Bits8 Bits8 where toFFI = id

export
ToFFI Bits16 Bits16 where toFFI = id

export
ToFFI Bits32 Bits32 where toFFI = id

export
ToFFI Bits64 Bits64 where toFFI = id

export
ToFFI Int8 Int8 where toFFI = id

export
ToFFI Int16 Int16 where toFFI = id

export
ToFFI Int32 Int32 where toFFI = id

export
ToFFI Int64 Int64 where toFFI = id

export
ToFFI Int Int where toFFI = id

export
ToFFI Char Char where toFFI = id

export
ToFFI Integer Integer where toFFI = id

export
ToFFI Double Double where toFFI = id

export
ToFFI String String where toFFI = id

||| Interface supporting the use of a value as a return type in a foreign function call.
public export
interface FromFFI a ffiRepr | a where
  fromFFI : ffiRepr -> Maybe a

export
FromFFI AnyPtr AnyPtr where fromFFI = Just

export
FromFFI Bits8 Bits8 where fromFFI = Just

export
FromFFI Bits16 Bits16 where fromFFI = Just

export
FromFFI Bits32 Bits32 where fromFFI = Just

export
FromFFI Bits64 Bits64 where fromFFI = Just

export
FromFFI Int8 Int8 where fromFFI = Just

export
FromFFI Int16 Int16 where fromFFI = Just

export
FromFFI Int32 Int32 where fromFFI = Just

export
FromFFI Int64 Int64 where fromFFI = Just

export
FromFFI Char Char where fromFFI = Just

export
FromFFI Int Int where fromFFI = Just

export
FromFFI Integer Integer where fromFFI = Just

export
FromFFI Double Double where fromFFI = Just

export
FromFFI String String where fromFFI = Just

