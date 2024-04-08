
type wsize =
| U8
| U16
| U32
| U64
| U128
| U256

type reg_kind =
| Normal
| Extra

type writable =
| Constant
| Writable

type reference =
| Direct
| Pointer of writable

type v_kind =
| Const
| Stack of reference
| Reg of (reg_kind * reference)
| Inline
| Global
