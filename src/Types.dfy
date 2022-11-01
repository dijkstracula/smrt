module NativeTypes {
    const UINT8_MAX := 0x100 - 1
    const UINT32_MAX := 0x1_0000_0000 - 1
    const UINT64_MAX := 0x1_0000_0000_0000_0000 - 1
    const USIZE_MAX := UINT64_MAX

    newtype{:nativeType "byte" } uint8 = i:int | 0 <= i <= UINT8_MAX
    newtype{:nativeType "ulong"} uint32 = i:int | 0 <= i <= UINT32_MAX
    newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i <= UINT64_MAX
    newtype{:nativeType "ulong"} usize  = i:int | 0 <= i <= USIZE_MAX

}

module Types {
    import opened NativeTypes

    datatype Pair<T> = Pair(b: T, e: T)
}