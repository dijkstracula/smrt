module NativeTypes {
    newtype{:nativeType "byte" } uint8 = i:int | 0 <= i < 0x100
    newtype{:nativeType "ulong"} uint32 = i:int | 0 <= i < 0x1_0000_0000
    newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x1_0000_0000_0000_0000
    newtype{:nativeType "ulong"} usize  = i:int | 0 <= i < 0x1_0000_0000_0000_0000
}

module Types {
    import opened NativeTypes

    datatype Pair<T> = Pair(b: T, e: T)
}