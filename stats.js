const res = require("./resfinal");
const _res = require("./_res");
const keys = Object.keys(res);
const arr = keys.map(k =>{return {altergo: _res[k]["altergo"], zm: _res[k]["zm"], "zm+arith": _res[k]["zm+arith"], ...res[k]}})
const unionarr = function() {return arr.filter(obj => [...arguments].reduce((p,v) => p + obj[v], 0) > -1*arguments.length);}
const diff = (l, lp) => l.filter(x => lp.indexOf(x) < 0);
const logunion = function() {
    let t = unionarr(...arguments);
    let x = t.length;
    console.log(x, "|", Math.floor(x/keys.length*1000+1/2)/10+"%", "// Proven by", ...[...arguments].map((s,i) => (i==0?"":"or ")+s.toUpperCase()));
}
console.log (" nb of proofs | Percentage of obligations proved");
console.log("Zenon Polarised ---------------------------------------------------------------------------");
logunion("zp");
logunion("zp", "zp+brwrt");
logunion("zp+arith");
logunion("zp+arith", "zp+arith+brwrt");
logunion("zp", "zp+brwrt", "zp+arith", "zp+arith+brwrt");
console.log("Zenon Modulo ------------------------------------------------------------------------------");
logunion("zm");
logunion("zm+arith");
logunion("zm", "zm+arith");
console.log("Zenon Modulo + Polarised -------------------------------------------------------------------");
logunion("zp", "zp+brwrt", "zp+arith", "zp+arith+brwrt", "zm", "zm+arith");
console.log("Altergo ------------------------------------------------------------------------------------");
logunion("altergo");
console.log("Everything ---------------------------------------------------------------------------------");
logunion("zp", "zp+brwrt", "zp+arith", "zp+arith+brwrt", "zm", "zm+arith", "altergo");
console.log("-------------ZP MINUS ZM")
console.log (diff (unionarr("zp", "zp+brwrt", "zp+arith", "zp+arith+brwrt"),
unionarr("zm", "zm+arith")).length);
console.log("-------------ZP MINUS ZM")
console.log (diff (unionarr("zm", "zm+arith"), unionarr("zp", "zp+brwrt", "zp+arith", "zp+arith+brwrt")).length);

