const x = {let f: {const g: true}};
const fun = (y: {let f: {}}) => { y.f = {}; };
const y = fun(x);
x.f.g;
