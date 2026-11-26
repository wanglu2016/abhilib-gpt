import {cases,edition,fragment} from './cases.mjs';
import {translate} from './grammar.mjs';
import {render,backtranslate,leanFile,termFile} from './logic.mjs';
import {termInfo,leanNames} from './vocabulary.mjs';
const $=id=>document.getElementById(id);
function node(tag,text,klass){
 const n=document.createElement(tag);if(text!==undefined)n.textContent=text;if(klass)n.className=klass;return n;
}
function button(label,action){const b=node('button',label);b.onclick=action;return b;}
function details(label,...children){const d=node('details');d.append(node('summary',label),...children);return d;}
function download(name,body,type){
 const url=URL.createObjectURL(new Blob([body],{type}));const a=node('a');
 a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),5000);
}
const store='AbhiLib.semanticReviews.v1';
let saved={};try{saved=JSON.parse(localStorage.getItem(store)||'{}');}catch{}
let example,context={},result=null,key='';
function drawList(){
 $('list').replaceChildren(...cases.map(c=>{
  const b=node('button');b.className='item'+(c.id===example?.id?' active':'');b.append(node('span',c.id),document.createTextNode(c.title));
  if(c.id===example?.id)b.setAttribute('aria-current','page');b.onclick=()=>select(c);return b;
 }));
}
function select(c,hash=true){
 example=c;context={...c?.defaults};$('input').value=c?.text||'';$('title').textContent=c?.title||'自擬命題';
 $('source').textContent=c?'《俱舍九題》第'+c.chapter+'題 · 書頁 '+c.page:'自由輸入 · 支援簡體與繁體';
 $('pdf').hidden=!c;if(c)$('pdf').href=edition+'#page='+c.page;
 $('provenance').textContent=c?c.voice+'。'+c.context:'可試「阿那含只成就無漏初靜慮」，或把例句中的否定、前後念、主詞和賓語改掉。';
 $('related').replaceChildren();
 if(c?.id==='02'||!c)$('related').append(button('比較「色界」的兩個義項',()=>{select(null);$('input').value='色界';convert();}));
 if(c?.id==='09')$('related').append(button('另試同段省略句「修淨非無漏」',()=>select(fragment)));
 if(c?.id===fragment.id)$('related').append(button('回到第 9 例的完整命題',()=>select(cases.find(x=>x.id==='09'))));
 $('restore').hidden=!c;$('check').textContent=c?.check||'檢查反譯是否保留了你所問的對象和限定。';
 if(hash)history.replaceState(null,'','#'+(c?.id||'new'));
 drawList();if(c)convert();else{invalidate();$('input').focus();}
}
function markOriginal(){
 const edited=example&&$('input').value!==example.text;
 $('original').textContent=edited?'你的改寫。書中原句為「'+example.text+'」':'';
 $('original').hidden=!edited;
}
function invalidate(){
 markOriginal();
 result=null;key='';$('status').textContent='待轉換';$('output').replaceChildren(node('p','用上方的原句重新轉換。','muted'));$('review').hidden=true;
 $('context').replaceChildren();
}
function contextLine(){
 const entries=Object.entries(context),d=$('context');d.replaceChildren();
 if(!entries.length)return;
 const names={dharma:'心不相應行.得',cultivation:'二修.得修',acquisition:'得捨.得',case:'四句中的開放條件',exists:'存在斷言',element:'十八界.色界',realm:'三界.色界',samapatti:'等至.淨',nature:'只限漏性',levels:'只限四地',both:'漏性與四地兩項限制'};
 d.append(document.createTextNode('採用的上下文　'+entries.map(([,v])=>names[v]||v).join(' · ')+'　'),button('清除上下文',()=>{context={};convert();}));
}
function reviewKey(){return JSON.stringify([example?.id||'new',$('input').value,Object.entries(context).sort(),result.status]);}
function loadReview(){
 key=reviewKey();const entry=saved[key]||{};$('judgment').value=entry.judgment||'';$('comment').value=entry.comment||'';$('review').hidden=false;
 const past=$('pastFormula');past.replaceChildren();
 if(entry.formula&&result.ast&&entry.formula!==render(result.ast))past.append(details('上次批註時的公式',node('pre',entry.formula)));

}
function record(){
 if(!key)return;
 saved[key]={example:example?.id||null,text:$('input').value,context:{...context},status:result.status,formula:result.ast?render(result.ast):result.term?.id||null,judgment:$('judgment').value,comment:$('comment').value};
 if(!saved[key].judgment&&!saved[key].comment)delete saved[key];
 try{localStorage.setItem(store,JSON.stringify(saved));}catch{$('review').querySelector('small').textContent='瀏覽器無法寫入記錄；請在離開前匯出。';}
}
function convert(){
 markOriginal();result=translate($('input').value,context);contextLine();const o=$('output');o.replaceChildren();
 if(result.status==='term'){
  const t=result.term;
  $('status').textContent='術語 · '+t.type;
  o.append(node('h3',t.id),node('p',t.gloss,'translation'),node('h3','Lean 表述'),node('pre',leanNames(t.lean)),
   node('small','« » 是 Lean 書寫漢字名稱所用的界符。'),
   button('下載術語 .lean',()=>download('術語.lean',termFile(t),'text/plain')));
  loadReview();return;
 }
 if(result.status!=='parsed'){
  $('status').textContent=result.status==='needs-context'?'待定義讀法':'未覆蓋';
  o.append(node('p',result.message,'panelnote'));
  if(result.options?.length){
   const choices=node('div',undefined,'choices'),field=result.field;
   for(const opt of result.options){
    const reading=translate($('input').value,{...context,[field]:opt.value});
    const card=node('div',undefined,'candidate');
    card.append(button(opt.label,()=>{context[field]=opt.value;convert();}));
    if(reading.ast)card.append(node('p',backtranslate(reading.ast)),details('候選公式',node('pre',render(reading.ast))));
    else if(reading.term)card.append(node('p',reading.term.type+'　'+reading.term.gloss));
    else card.append(node('p',reading.message));
    choices.append(card);
   }
   o.append(choices);
  }
  loadReview();return;
 }
 const {ast,trace,symbols}=result;$('status').textContent=ast.op==='open'?'開放條件 · 人位 → Prop':'命題 · Prop';
 o.append(node('h3','公式反譯'),node('p',backtranslate(ast),'translation'),node('h3','邏輯式'),node('pre',render(ast)),
  node('small','法指所論的個例，人位指一位有情在某一時的狀態。∀ 表示每一個，∃ 表示至少一個。'));
 if(trace.length){const ul=node('ul');trace.forEach(t=>ul.append(node('li',t)));o.append(node('h3','採用的解讀'),ul);}
 const dl=node('dl');symbols.forEach(id=>{const v=termInfo(id);dl.append(node('dt',v.id),node('dd',v.type+'。'+v.gloss));});
 o.append(details('所用術語與關係',dl),
  details('Lean 表述與下載',node('p','檔案定義一個依賴指定解釋的公式，Lean 可以檢查型別。公式的真值及譯義由另一步審定。','muted'),node('pre',render(ast,'lean')),button('下載完整 .lean',()=>download('譯句.lean',leanFile([ast]),'text/plain'))),
  details('查看語法樹 JSON',node('pre',JSON.stringify(ast,null,2))));
 loadReview();
}
$('input').oninput=()=>{context={};invalidate();};$('convert').onclick=convert;$('blank').onclick=()=>select(null);
$('restore').onclick=()=>select(example);$('judgment').onchange=record;$('comment').oninput=record;
$('export').onclick=()=>download('AbhiLib-審讀.json',JSON.stringify({version:1,reviews:Object.values(saved)},null,2),'application/json');
function fromHash(){
 const hash=location.hash.slice(1);
 if(hash==='sejie'){select(null,false);$('input').value='色界';convert();return;}
 select(hash==='new'?null:[...cases,fragment].find(c=>c.id===hash)||cases[0],false);
}
window.addEventListener('hashchange',fromHash);
fromHash();
