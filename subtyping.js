const fun = (x: {let f: Num}) => 2 * x.f;
fun({let f: 0}) + fun({let f: 1, let g: 2})
