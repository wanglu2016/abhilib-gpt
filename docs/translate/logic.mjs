import {vocab,relations} from './vocabulary.mjs';
import {signature} from './model.mjs';

export const pred=(id,v)=>({op:'pred',id,v});
export const rel=(id,a,b)=>({op:'rel',id,a,b});
export const not=x=>({op:'not',x});
export const and=(...xs)=>({op:'and',xs});
export const or=(...xs)=>({op:'or',xs});
export const imp=(l,r)=>({op:'imp',l,r});
export const iff=(l,r)=>({op:'iff',l,r});
export const bind=(op,v,sort,body)=>({op,v,sort,body});
export const all=(v,sort,body)=>bind('all',v,sort,body);
export const some=(v,sort,body)=>bind('some',v,sort,body);

const sortName={D:'法例',S:'人於一時'};
export function inspect(root){
 const symbols=new Set();
 function check(n,env){
  function arg(v,sort){if(env[v]!==sort)throw Error('變元 '+v+' 所需類型為 '+sort);}
  if(n.op==='pred'){arg(n.v,vocab[n.id].sort);symbols.add(n.id);}
  else if(n.op==='rel'){const r=relations[n.id];arg(n.a,r.sorts[0]);arg(n.b,r.sorts[1]);symbols.add(n.id);}
  else if(['all','some','open'].includes(n.op)){
   if(!sortName[n.sort]||env[n.v])throw Error('變元重複或論域不明');
   check(n.body,{...env,[n.v]:n.sort});
  }else if(n.op==='not')check(n.x,env);
  else if(n.op==='and'||n.op==='or'){if(n.xs.length<2)throw Error('缺少邏輯項');n.xs.forEach(x=>check(x,env));}
  else if(n.op==='imp'||n.op==='iff'){check(n.l,env);check(n.r,env);}
  else throw Error('無此邏輯節點');
 }
 check(root,{});
 return [...symbols];
}
export function render(root,mode='formula'){
 const zh=mode==='chinese', lean=mode==='lean';
 function visit(n){
  if(n.op==='pred'){
   const p=vocab[n.id];
   if(lean)return '('+p.lean+') '+n.v;
   return zh?n.v+' 屬於「'+p.label+'」':p.label+'('+n.v+')';
  }
  if(n.op==='rel'){
   const r=relations[n.id];
   if(lean)return r.lean+' '+n.a+' '+n.b;
   if(zh)return n.id==='next'?n.b+' 可以緊接在 '+n.a+' 之後（同一相續）':n.a+' '+r.label+' '+n.b;
   return ({next:'無間後繼',now:'現前',gains:'得',owns:'成就',active:'習修',acquired:'得修',assoc:'相應'})[n.id]+'('+n.a+', '+n.b+')';
  }
  if(n.op==='not')return (zh?'不成立的是「':'¬ (')+visit(n.x)+(zh?'」':')');
  if(n.op==='and'||n.op==='or'){
   const join=n.op==='and'?(zh?' 並且 ':' ∧ '):(zh?' 或者 ':' ∨ ');
   return '('+n.xs.map(visit).join(join)+')';
  }
  if(n.op==='imp'||n.op==='iff'){
   if(zh)return n.op==='imp'?'若「'+visit(n.l)+'」，則「'+visit(n.r)+'」':'「'+visit(n.l)+'」當且僅當「'+visit(n.r)+'」';
   return '('+visit(n.l)+(n.op==='imp'?' → ':' ↔ ')+visit(n.r)+')';
  }
  const q={all:'∀',some:'∃',open:lean?'fun':'λ'}[n.op];
  if(zh)return ({all:'對每一個',some:'至少有一個',open:'對給定的'})[n.op]+sortName[n.sort]+' '+n.v+'，'+(n.op==='open'?'檢查以下條件：':'')+visit(n.body);
  if(lean)return '('+q+' ('+n.v+' : w.'+n.sort+')'+(n.op==='open'?' => ':', ')+visit(n.body)+')';
  return '('+q+n.v+' : '+n.sort+'，'+visit(n.body)+')';
 }
 return visit(root);
}
export function leanFile(roots){
 return signature+'\n'+roots.map((root,i)=>{
  inspect(root);
  const type=root.op==='open'?'w.'+root.sort+' → Prop':'Prop';
  return 'def reading'+(i+1)+' (w : Reading) : '+type+' :=\n  '+render(root,'lean');
 }).join('\n\n')+'\n\nend AbhiReading\n';
}

// The paraphrase reads only the tree. Preserve the variable of every witness.
export function backtranslate(root){
 function classifier(n,v){
  if(n.op==='pred'&&n.v===v)return vocab[n.id].label;
  if(n.op==='not'){
   const inner=classifier(n.x,v);
   return inner?'非「'+inner+'」':null;
  }
  if(n.op==='and'||n.op==='or'){
   const parts=n.xs.map(x=>classifier(x,v));
   if(parts.every(Boolean))return parts.join(n.op==='and'?'、且':'或');
  }
  return null;
 }
 function person(v){return v==='s'?'此人於此時':'該人位 '+v;}
 function action(pair,v){
  if(pair.op==='rel'&&pair.b===v&&['owns','gains','now'].includes(pair.id))
   return [person(pair.a),{owns:'成就',gains:'得到',now:'現起'}[pair.id]];
  if(pair.op==='or'&&pair.xs.length===2){
   const [a,b]=pair.xs;
   if(a.id==='active'&&b.id==='acquired'&&a.a===b.a&&a.b===v&&b.b===v)
    return [person(a.a),'習修或得修'];
  }
  return null;
 }
 function read(n){
  if(n.op==='not'&&n.x.op==='some'){
   const inner=read(n.x);
   return '下述情形無一例成立：'+inner;
  }
  if(n.op==='not')return '以下判斷不成立：「'+read(n.x)+'」';
  if(n.op==='some'&&n.body.op==='some'&&n.body.body.op==='and'){
   const [a,b,r]=n.body.body.xs;
   if(r?.op==='rel'&&r.a===n.v&&r.b===n.body.v){
    const left=classifier(a,n.v),right=classifier(b,n.body.v);
    if(r.id==='next')return '容有同一相續的兩念，前念符合「'+left+'」，緊接的後念符合「'+right+'」';
    if(r.id==='assoc')return '容有兩個相應的法，其中一個符合「'+left+'」，另一個符合「'+right+'」';
   }
  }
  if(n.op==='some'&&n.body.op==='and'){
   const [scope,r]=n.body.xs;
   const term=classifier(scope,n.v),act=action(r,n.v);
   if(term&&act)return act[0]+act[1]+'至少一個符合「'+term+'」的法';
   const other=r.op==='not'?classifier(r.x,n.v):classifier(r,n.v);
   if(term&&other)return '至少有一個'+term+'，'+(r.op==='not'?'不屬於':'屬於')+other;
   if(n.sort==='S')return '至少有一個人位 '+n.v+' 滿足以下兩項。'+read(n.body);
  }
  if(n.op==='all'&&n.body.op==='iff'){
   const a=classifier(n.body.l,n.v),b=classifier(n.body.r,n.v);
   if(a&&b)return '逐一看每個'+sortName[n.sort]+'，屬於「'+a+'」與屬於「'+b+'」互為充分必要條件';
  }
  if(n.op==='all'&&n.body.op==='imp'){
   const {l,r}=n.body,sub=classifier(l,n.v);
   if(sub&&r.op==='and'&&r.xs.every(k=>k.op==='not'&&classifier(k.x,n.v)))
    return '凡是「'+sub+'」，'+r.xs.map(k=>'不屬於「'+classifier(k.x,n.v)+'」').join('，也');
   if(sub&&r.op==='not'&&classifier(r.x,n.v))return '凡是「'+sub+'」，都不屬於「'+classifier(r.x,n.v)+'」';
   const obj=classifier(r,n.v);
   if(sub&&obj)return '凡是「'+sub+'」，都屬於「'+obj+'」';
   if(n.sort==='S'&&sub)return '對每位符合「'+sub+'」的有情，在該時位，'+read(r);
   if(n.sort==='S'&&l.op==='and'){
    const [state,cond]=l.xs;
    if(classifier(state,n.v))return '對每位符合「'+classifier(state,n.v)+'」的有情，若'+read(cond)+'，則'+read(r);
   }
  }
  if(n.op==='open')return '給定一位有情及一個時位，逐項檢查。'+read(n.body)+'。這裡列出判準，尚待代入人位';
  if(n.op==='and')return n.xs.map(read).join('。同時，');
  return render(n,'chinese');
 }
 return read(root)+'。';
}
