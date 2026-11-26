import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {translate} from '../docs/translate/grammar.mjs';
import {vocab,relations,realmNames,termInfo} from '../docs/translate/vocabulary.mjs';
import {cases,fragment} from '../docs/translate/cases.mjs';
import {leanFile,inspect,backtranslate,render,termFile} from '../docs/translate/logic.mjs';

function ast(text,context){
 const result=translate(text,context);
 assert.equal(result.status,'parsed',text+' '+(result.message||''));
 return result.ast;
}
const samples=cases.map(c=>ast(c.text,c.defaults));
assert.deepEqual(samples.map(x=>x.op),['all','all','some','some','not','all','and','all','all','all']);
for(const tree of samples){assert.ok(inspect(tree).length);assert.ok(backtranslate(tree).length>10);}
assert.equal(samples[1].body.op,'iff');
assert.equal(ast('色處是十八界中的色界').body.op,'imp');
assert.deepEqual(ast('色界等於色處',{sejie:'element'}),samples[1]);
assert.equal(translate('色界等於色處').field,'sejie');
assert.equal(translate('色界等於色處',{sejie:'realm'}).status,'unsupported');
assert.deepEqual(ast('十八界.色界等於十二處.色處'),samples[1]);
assert.deepEqual(ast('十八界．色界等于十二处．色处'),samples[1]);
assert.equal(translate('三界.色界等於十二處.色處').status,'unsupported');
assert.equal(ast('三界.色界等於三界.色界').op,'realmEq');
assert.equal(ast('三界.色界非三界.欲界').op,'not');
assert.equal(translate('色界').field,'sejie');
assert.equal(translate('色界',{sejie:'realm'}).term.type,'三界');
assert.equal(translate('色界',{sejie:'element'}).term.type,'法 → Prop');
assert.equal(translate('得',{gainSense:'dharma'}).term.id,'心不相應行.得');
assert.equal(translate('阿那含得初靜慮').field,'gainSense');
assert.equal(ast('得是心不相應行').body.l.id,'心不相應行.得');
assert.equal(ast('阿那含二修.得修初靜慮').body.r.body.xs[1].id,'二修.得修');
assert.match(render(ast('生於三界.色界的聖者成就初靜慮'),'lean'),/«生於» «釋» «三界»\.«色界»/);
assert.match(render(ast('色界繫非欲界繫'),'lean'),/«繫於» «釋» «三界»\.«色界»/);
assert.match(render(samples[2],'lean'),/«釋»\.«業道» x/);
assert.deepEqual(ast('三界.色界善心可以由三界.欲界善心無間而生'),samples[3]);
for(const id of [...Object.keys(vocab),...Object.keys(relations),...realmNames]){
 assert.match(id,/^[\p{Script=Han}]+(?:\.[\p{Script=Han}]+)*$/u);
 assert.equal(translate(id).term.id,id);
}
assert.deepEqual(ast('有业道而非业'),samples[2]);
assert.deepEqual(ast('有些業道不是業'),samples[2]);
assert.deepEqual(ast('色界善心可以由欲界善心無間而生'),samples[3]);
assert.deepEqual(ast('无学心不能无间生学心'),samples[4]);
assert.notDeepEqual(ast('學心不能無間生無學心'),samples[4]);
assert.deepEqual(ast('只有業道才是業'),ast('業是業道'));
assert.deepEqual(ast('只要是業道，就是業'),ast('業道是業'));
assert.deepEqual(ast('所有不還者都是聖者'),ast('阿那含是聖者'));
assert.equal(ast('阿那含是聖者').sort,'人位');
assert.equal(ast('阿那含必然成就初靜慮').body.r.body.xs[0].id,'初靜慮');
assert.deepEqual(['成就','現前','得捨.得'].map(v=>ast('阿那含'+v+'初靜慮').body.r.body.xs[1].id),['成就','現前','得捨.得']);
assert.equal(translate('修淨非無漏').field,'level');
assert.equal(translate('修淨非無漏',{level:'初靜慮'}).field,'closure');
assert.equal(ast('修淨非無漏',{level:'第二靜慮',closure:'exists'}).op,'some');
const openCase=ast(fragment.text,fragment.defaults);
assert.deepEqual(ast('修淨初靜慮非修無漏初靜慮',{closure:'case'}),openCase);
assert.equal(translate(cases[8].text).field,'level');
assert.equal(translate(cases[8].text,{level:'初靜慮'}).field,'gainSense');
assert.equal(samples[8].body.r.body.xs[1].id,'二修.得修');
assert.equal(ast(cases[8].text,{level:'初靜慮',gainSense:'acquisition'}).body.r.body.xs[1].id,'得捨.得');
assert.deepEqual(ast('習無漏時，若得修淨初靜慮，必得修無漏初靜慮').body.r,samples[8].body.r);
assert.equal(translate('只成就無漏初靜慮').field,'subject');
const only='阿那含只成就無漏初靜慮';
assert.equal(translate(only).field,'only');
for(const bad of ['constructor','色界等於色界','有業道非業且天氣晴','善是有情','苦根能無間生學心','學心和苦根能無間生學心','苦根通三性：善、善、無記','上界有情不成就學心和無學心','']){
 assert.equal(translate(bad).status,'unsupported',bad);
}
assert.throws(()=>inspect({op:'rel',id:'成就',a:'s',b:'d'}));

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
const mixed={法:['a','b'],facts:[['業道','a'],['業道','b'],['業','a']]};
assert.equal(evaluate(samples[2],mixed),true);
assert.equal(evaluate(ast('業道非業'),mixed),false);
assert.equal(evaluate(ast('并非所有业道都是业'),mixed),true);
const state={人位:['p'],法:['a','b'],facts:[['不還者','p'],['初靜慮','a'],['無漏','a'],['初靜慮','b'],['有漏','b'],['成就','p','a'],['成就','p','b']]};
assert.equal(evaluate(ast(only,{only:'nature'}),state),false);
assert.equal(evaluate(ast(only,{only:'levels'}),state),true);
assert.equal(evaluate(ast('阿那含成就无漏初静虑和有漏初静虑'),state),true);
assert.equal(evaluate(ast('阿那含现前无漏初静虑'),state),false);
const exception={人位:['p'],法:['d'],facts:[['生上二界','p'],['心','d'],['欲界繫','d']]};
assert.equal(evaluate(samples[5],exception),true); // no entitlement to the exception
exception.facts.push(['成就','p','d']);
assert.equal(evaluate(samples[5],exception),false);
exception.facts.push(['通果心','d']);
assert.equal(evaluate(samples[5],exception),true);
const twoPeople={人位:['p','q'],法:['a','b'],facts:[['生欲界','p'],['無漏律儀','a'],['靜慮律儀','b'],['成就','p','a'],['成就','q','b']]};
assert.equal(evaluate(samples[9],twoPeople),false);
twoPeople.facts.push(['成就','p','b']);
assert.equal(evaluate(samples[9],twoPeople),true);

if(process.argv.includes('--lean')){
 const dir=mkdtempSync(join(tmpdir(),'abhi-readings-'));
 try{
  const path=join(dir,'Readings.lean');
  const smoke=`
namespace AbhiLib.«命題譯讀»
example («釋» : «詮釋») (h : «譯句2» «釋») (d : «釋».«法») (hd : «十八界».«色界» «釋» d) :
    «十二處».«色處» «釋» d := (h d).mp hd

example («釋» : «詮釋») (h : «譯句3» «釋») : ∃ x, ¬ «釋».«業» x := by
  obtain ⟨x, _, hx⟩ := h
  exact ⟨x, hx⟩

example («釋» : «詮釋») (s : «釋».«人位») : Prop := «譯句11» «釋» s
example : «三界» := «三界».«色界»
example («釋» : «詮釋») : «釋».«法» → Prop := «十八界».«色界» «釋»
end AbhiLib.«命題譯讀»
`;
  writeFileSync(path,leanFile([...samples,openCase,ast(only,{only:'levels'}),ast('慧能與學心相應')])+smoke);
  execFileSync('lean',[path],{stdio:'inherit'});
  const ids=[...Object.keys(vocab),...Object.keys(relations),...realmNames];
  const terms=ids.map(id=>termFile(termInfo(id)).split('namespace AbhiLib.«命題譯讀»').at(-1).split('end AbhiLib.')[0]);
  writeFileSync(path,leanFile([ast('三界.色界不等於三界.欲界')])+'\nnamespace AbhiLib.«命題譯讀»\n'+terms.join('\n')+'\nend AbhiLib.«命題譯讀»\n');
  execFileSync('lean',[path],{stdio:'inherit'});
 }finally{rmSync(dir,{recursive:true});}
}
console.log('10 source readings, contrastive rewrites, scope and finite-interpretation checks passed.');
