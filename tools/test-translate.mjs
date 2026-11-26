import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {translate} from '../docs/translate/grammar.mjs';
import {cases} from '../docs/translate/cases.mjs';
import {leanFile,inspect,backtranslate} from '../docs/translate/logic.mjs';

function ast(text,context){
 const result=translate(text,context);
 assert.equal(result.status,'parsed',text+' '+(result.message||''));
 return result.ast;
}
const samples=cases.map(c=>ast(c.text,c.defaults));
assert.deepEqual(samples.map(x=>x.op),['all','all','some','some','not','all','and','all','open','all']);
for(const tree of samples){assert.ok(inspect(tree).length);assert.ok(backtranslate(tree).length>10);}
assert.equal(samples[1].body.op,'iff');
assert.equal(ast('色處是十八界中的色界').body.op,'imp');
assert.deepEqual(ast('色界等於色處',{sejie:'element'}),samples[1]);
assert.equal(translate('色界等於色處').field,'sejie');
assert.notDeepEqual(ast('色界等於色處',{sejie:'realm'}),samples[1]);
assert.deepEqual(ast('有业道而非业'),samples[2]);
assert.deepEqual(ast('有些業道不是業'),samples[2]);
assert.deepEqual(ast('色界善心可以由欲界善心無間而生'),samples[3]);
assert.deepEqual(ast('无学心不能无间生学心'),samples[4]);
assert.notDeepEqual(ast('學心不能無間生無學心'),samples[4]);
assert.deepEqual(ast('只有業道才是業'),ast('業是業道'));
assert.deepEqual(ast('只要是業道，就是業'),ast('業道是業'));
assert.deepEqual(ast('所有不還者都是聖者'),ast('阿那含是聖者'));
assert.equal(ast('阿那含是聖者').sort,'S');
assert.equal(ast('阿那含必然成就初靜慮').body.r.body.xs[0].id,'level0');
assert.deepEqual(['成就','現前','得'].map(v=>ast('阿那含'+v+'初靜慮').body.r.body.xs[1].id),['owns','now','gains']);
assert.equal(translate('修淨非無漏').field,'level');
assert.equal(translate('修淨非無漏',{level:'初靜慮'}).field,'closure');
assert.equal(ast('修淨非無漏',{level:'第二靜慮',closure:'exists'}).op,'some');
assert.deepEqual(ast('修淨初靜慮非修無漏初靜慮',{closure:'case'}),samples[8]);
assert.equal(translate('只成就無漏初靜慮').field,'subject');
const only='阿那含只成就無漏初靜慮';
assert.equal(translate(only).field,'only');
for(const bad of ['有業道非業且天氣晴','善是有情','苦根能無間生學心','學心和苦根能無間生學心','苦根通三性：善、善、無記','上界有情不成就學心和無學心','']){
 assert.equal(translate(bad).status,'unsupported',bad);
}
assert.throws(()=>inspect({op:'rel',id:'owns',a:'s',b:'d'}));

// Independent finite interpretations distinguish statements that look similar.
// Predicate extensions in these tiny structures serve only as translation tests.
function evaluate(tree,model,env={}){
 const lookup=([id,...args])=>model.facts.some(f=>JSON.stringify(f)===JSON.stringify([id,...args]));
 const holds=n=>evaluate(n,model,env);
 switch(tree.op){
  case 'pred':return lookup([tree.id,env[tree.v]]);
  case 'rel':return lookup([tree.id,env[tree.a],env[tree.b]]);
  case 'not':return !holds(tree.x);
  case 'and':return tree.xs.every(holds);
  case 'or':return tree.xs.some(holds);
  case 'imp':return !holds(tree.l)||holds(tree.r);
  case 'iff':return holds(tree.l)===holds(tree.r);
  case 'all':case 'some':{
   const test=value=>evaluate(tree.body,model,{...env,[tree.v]:value});
   return tree.op==='all'?model[tree.sort].every(test):model[tree.sort].some(test);
  }
  default:throw Error('open or unknown expression');
 }
}
const mixed={D:['a','b'],facts:[['path','a'],['path','b'],['karma','a']]};
assert.equal(evaluate(samples[2],mixed),true);
assert.equal(evaluate(ast('業道非業'),mixed),false);
assert.equal(evaluate(ast('并非所有业道都是业'),mixed),true);
const state={S:['p'],D:['a','b'],facts:[['nonreturn','p'],['level0','a'],['undefiled','a'],['level0','b'],['outflow','b'],['owns','p','a'],['owns','p','b']]};
assert.equal(evaluate(ast(only,{only:'nature'}),state),false);
assert.equal(evaluate(ast(only,{only:'levels'}),state),true);
assert.equal(evaluate(ast('阿那含成就无漏初静虑和有漏初静虑'),state),true);
assert.equal(evaluate(ast('阿那含现前无漏初静虑'),state),false);
const exception={S:['p'],D:['d'],facts:[['upperBorn','p'],['mind','d'],['desire','d']]};
assert.equal(evaluate(samples[5],exception),true); // no entitlement to the exception
exception.facts.push(['owns','p','d']);
assert.equal(evaluate(samples[5],exception),false);
exception.facts.push(['supernormal','d']);
assert.equal(evaluate(samples[5],exception),true);
const twoPeople={S:['p','q'],D:['a','b'],facts:[['borndesire','p'],['discipline','a'],['meditative','b'],['owns','p','a'],['owns','q','b']]};
assert.equal(evaluate(samples[9],twoPeople),false);
twoPeople.facts.push(['owns','p','b']);
assert.equal(evaluate(samples[9],twoPeople),true);

if(process.argv.includes('--lean')){
 const dir=mkdtempSync(join(tmpdir(),'abhi-readings-'));
 try{
  const path=join(dir,'Readings.lean');
  const smoke=`
namespace AbhiReading
example (w : Reading) (h : reading2 w) (d : w.D) (hd : w.dharmaMark .visibleElement d) :
    w.dharmaMark .visibleBase d := (h d).mp hd

example (w : Reading) (h : reading3 w) : ∃ x, ¬ w.dharmaMark .karma x := by
  obtain ⟨x, _, hx⟩ := h
  exact ⟨x, hx⟩

example (w : Reading) (s : w.S) : Prop := reading9 w s
end AbhiReading
`;
  writeFileSync(path,leanFile([...samples,ast(only,{only:'levels'}),ast('慧能與學心相應')])+smoke);
  execFileSync('lean',[path],{stdio:'inherit'});
 }finally{rmSync(dir,{recursive:true});}
}
console.log('10 source readings, contrastive rewrites, scope and finite-interpretation checks passed.');
