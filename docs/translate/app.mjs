import {cases,edition} from './cases.mjs';
import {translate} from './grammar.mjs';
import {render,backtranslate,leanFile} from './logic.mjs';
import {vocab,relations} from './vocabulary.mjs';
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
 const names={case:'四句中的開放條件',exists:'存在斷言',element:'十八界色境',realm:'三界色界',nature:'只限漏性',levels:'只限四地',both:'漏性與四地兩項限制'};
 d.append(document.createTextNode('採用的上下文　'+entries.map(([,v])=>names[v]||v).join(' · ')+'　'),button('清除上下文',()=>{context={};convert();}));
}
function reviewKey(){return JSON.stringify([example?.id||'new',$('input').value,Object.entries(context).sort(),result.status]);}
function loadReview(){
 key=reviewKey();const entry=saved[key]||{};$('judgment').value=entry.judgment||'';$('comment').value=entry.comment||'';$('review').hidden=false;
}
function record(){
 if(!key)return;
 saved[key]={example:example?.id||null,text:$('input').value,context:{...context},status:result.status,formula:result.ast?render(result.ast):null,judgment:$('judgment').value,comment:$('comment').value};
 if(!saved[key].judgment&&!saved[key].comment)delete saved[key];
 try{localStorage.setItem(store,JSON.stringify(saved));}catch{$('review').querySelector('small').textContent='瀏覽器無法寫入記錄；請在離開前匯出。';}
}
function convert(){
 markOriginal();result=translate($('input').value,context);contextLine();const o=$('output');o.replaceChildren();
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
    else card.append(node('p',reading.message));
    choices.append(card);
   }
   o.append(choices);
  }
  loadReview();return;
 }
 const {ast,trace,symbols}=result;$('status').textContent=ast.op==='open'?'開放條件 · S → Prop':'命題 · Prop';
 o.append(node('h3','公式反譯'),node('p',backtranslate(ast),'translation'),node('h3','邏輯式'),node('pre',render(ast)),
  node('small','D 是法的個例，S 是一位有情的一個時位。∀ 表示每一個，∃ 表示至少一個。'));
 if(trace.length){const ul=node('ul');trace.forEach(t=>ul.append(node('li',t)));o.append(node('h3','採用的解讀'),ul);}
 const dl=node('dl');symbols.forEach(id=>{const v=vocab[id]||relations[id];dl.append(node('dt',v.label),node('dd',v.gloss));});
 o.append(details('所用術語與關係',dl),
  details('Lean 表述與下載',node('p','檔案定義一個依賴指定解釋的公式，Lean 可以檢查型別。公式的真值及譯義由另一步審定。','muted'),node('pre',render(ast,'lean')),button('下載完整 .lean',()=>download('Reading.lean',leanFile([ast]),'text/plain'))),
  details('查看語法樹 JSON',node('pre',JSON.stringify(ast,null,2))));
 loadReview();
}
$('input').oninput=()=>{context={};invalidate();};$('convert').onclick=convert;$('blank').onclick=()=>select(null);
$('restore').onclick=()=>select(example);$('judgment').onchange=record;$('comment').oninput=record;
$('export').onclick=()=>download('AbhiLib-審讀.json',JSON.stringify({version:1,reviews:Object.values(saved)},null,2),'application/json');
function fromHash(){
 const hash=location.hash.slice(1);
 select(hash==='new'?null:cases.find(c=>c.id===hash)||cases[0],false);
}
window.addEventListener('hashchange',fromHash);
fromHash();
