const res = require("./res");
const _res = require("./_res");
const keys = Object.keys(res);
const arr = keys.map(k =>{return {..._res[k], ...res[k]}})
const unionarr = function() {
	
	const aux = arr.filter(obj => 
		[...arguments]
		.reduce((p,v) => p + obj[v], 0) > -1*arguments.length)
			.map(obj => {
				const ret = {};
		[...arguments].forEach(k => ret[k] = obj[k]);
				return ret
	});
	return aux
}
const diff = function(a, b) {

        const aux = arr.filter(obj =>
                [...a]
                .reduce((p,v) => p + obj[v], 0) > -1*a.length
		&& ! ([...b]
		.reduce((p,v) => p + obj[v], 0) > -1*a.length)
	)
                        .map(obj => {
                                const ret = {};
                [...a].forEach(k => ret[k] = obj[k]);
                                return ret
        });
        return aux
}
;
const logunion = function() {
    let t = unionarr(...arguments);
    let x = t.length;
    console.log(x, "|", Math.floor(x/keys.length*1000+1/2)/10+"%", "// Proven by", ...[...arguments].map((s,i) => (i==0?"":"or ")+s.toUpperCase()));
}
console.log(...Object.keys(res[keys[0]]), ...Object.keys(_res[keys[0]]));
console.log (" nb of proofs | Percentage of obligations proved");
const zp = ["zp", "zp+brwrt", "zp+sko", "zp+brwrt+sko", "zp+sko+mini", "zp+brwrt+sko+mini", "zp+arith", "zp+brwrt+arith", "zp+sko+arith", "zp+brwrt+sko+arith", "zp+sko+mini+arith", "zp+brwrt+sko+mini+arith"];
const zm = ["zm", "zm+arith"];
logunion(...zp);
logunion(...zm);
logunion("altergo");
logunion("altergo", ...zp, ...zm);

const avg_med = t => {
	const arr = unionarr(...t).map(e => Math.min(...Object.values(e).filter(e=>e!==-1))); 
	arr.sort();
	return [Math.floor(100*arr.reduce((a,b)=>a+b,0)/arr.length)/100, arr[Math.floor(arr.length/2)]]
};

console.log("avg_med time zp:", avg_med(zp), "\navg_med time zm:", avg_med(zm), "\navg_med time altergo:", avg_med(["altergo"]), "\navg_med time total:", avg_med(["altergo", ...zp, ...zm]))


const logdiff = (a,b) => {
	const dab = diff(a,b).map(e=>Math.min(...Object.values(e).filter(e=>e!==-1)));
	return [dab.length, Math.floor(100*dab.reduce((a,b)=>a+b, 0)/dab.length)/100, "ms"]
}

console.log("altergo-zm: ", ...logdiff(["altergo"], zm));
console.log("zm-altergo: ", ...logdiff(zm, ["altergo"]));

console.log("altergo-zp: ", ...logdiff(["altergo"], zp));
console.log("zp-altergo: ", ...logdiff(zp, ["altergo"]));

console.log("zp-zm: ", ...logdiff(zp, zm));
console.log("zm-zp: ", ...logdiff(zm, zp));

console.log("altergo-zm-zp: ", ...logdiff(["altergo"], [...zm,...zp]));
console.log("zp-zm-altergo: ", ...logdiff(zp, [...zm, "altergo"]));
console.log("zm-zp-altergo: ", ...logdiff(zm, [...zp, "altergo"]));

const sko = zp.filter(e=>e.includes("sko") && !e.includes("mini"));
const mini = zp.filter(e=>e.includes("mini"));
const reste = zp.filter(e=>!e.includes("sko") && !e.includes("mini"));

console.log(sko, mini, reste)

console.log("sko", avg_med(sko));
console.log("mini", avg_med(mini));
console.log("reste", avg_med(reste));

console.log("sko-mini", ...logdiff(sko, mini));
console.log("mini-sko", ...logdiff(mini, sko));

console.log("sko-reste", ...logdiff(sko, reste));
console.log("reste-sko", ...logdiff(reste, sko));

console.log("reste-mini", ...logdiff(reste, mini));
console.log("mini-reste", ...logdiff(mini, reste));

logunion(...sko);
logunion(...mini);
logunion(...reste);

const brwrt = zp.filter(e=>e.includes("brwrt"));
const negbrwrt = zp.filter(e=>!e.includes("brwrt"));

console.log("brwrt-reste", ...logdiff(brwrt, negbrwrt));
console.log("reste-brwrt", ...logdiff(negbrwrt, brwrt));

