const fun1 = (x: {f: Num, g: Num} ) => x.f + x.g;
const fun2 = (x: {f: Num}) => x.f;
fun2({f: 0})
