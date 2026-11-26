import {vocab,realmNames,termInfo,relations} from './vocabulary.mjs';
import {traditional} from './characters.mjs';
import {pred,rel,not,and,or,imp,iff,all,some,bind,inspect} from './logic.mjs';

const names=new Map();
for(const term of Object.values(vocab)){
 for(const name of [term.id,...term.aliases]){
  if(names.has(name)&&names.get(name)!==term.id)throw Error('詞彙有重名，須指定分類：'+name);
  names.set(name,term.id);
 }
}
const levels=['初','第二','第三','第四'];
const levelNames=levels.map(x=>x+'靜慮');
const realmIds={'欲界':'欲界繫','色界':'色界繫','無色界':'無色界繫'};
const sortLabel={法:'法類',人位:'有情或其時位'};
const simple=s=>[...s].map(c=>traditional[c]||c).join('').replaceAll('爲','為');
const conjunction=xs=>xs.length===1?xs[0]:and(...xs);
const disjunction=xs=>xs.length===1?xs[0]:or(...xs);
const mindIds=new Set(['心','學心','無學心','通果心']);
function denotesMind(n){
 if(n.op==='pred')return mindIds.has(n.id);
 if(n.op==='and')return n.xs.some(denotesMind);
 if(n.op==='or')return n.xs.every(denotesMind);
 return false;
}

class Issue extends Error{
 constructor(message,field,options){super(message);this.field=field;this.options=options;}
}
function fail(text){throw new Issue(text);}
function choose(context,field,options,message){
 if(!options.some(o=>o.value===context[field]))throw new Issue(message,field,options);
 return context[field];
}
function realmValue(term){
 const name=term.replace(/^三界(?:中的|中)/,'三界.');
 if(realmNames.includes(name))return name;
 if(['欲界','無色界'].includes(name))return '三界.'+name;
 return null;
}
function reader(context,trace){
 function note(s){if(!trace.includes(s))trace.push(s);}
 function atom(s,sort,v){
  if(s==='色界'){
   if(sort!=='法')fail('此處需要有情或人位，請明寫例如「生色界的聖者」。');
   const reading=choose(context,'sejie',[{value:'element',label:'十八界.色界（色境）'},{value:'realm',label:'三界.色界（生地或所繫之界）'}],'單說「色界」可以是色境，也可以是法所繫的色界。');
   if(reading==='realm')fail('「三界.色界」是界名。要談法的繫屬，請寫「色界繫」；要談有情的生地，請寫「生於三界.色界」。');
   note('此處「色界」依所選讀法指十八界.色界。');
   return pred('十八界.色界',v);
  }
  if(realmValue(s))fail('「'+s+'」是界名。此處需要法類或人位條件，請明寫所繫或生地。');
  if(s==='得'&&sort==='法'){
   note('「得」在法類的位置，取心不相應行.得。');
   return pred('心不相應行.得',v);
  }
  const found=names.get(s);
  if(found){
   if(vocab[found].sort!==sort)fail('「'+s+'」是'+sortLabel[vocab[found].sort]+'，此處需要'+sortLabel[sort]+'。');
   if(levelNames.includes(found))note('「靜慮」未標近分時依根本等至解讀。定地本身不限定漏性。');
   if(found==='等至.淨'&&s==='淨')fail('單詞「淨」需要指出所修的定，或寫明「淨初靜慮」等。');
   return pred(found,v);
  }
  if(sort==='人位'){
   const match=s.match(/^生(?:於)?(?:三界\.)?(欲界|無色界|色界)(?:的)?(聖者|阿羅漢|不還者|阿那含|有情)$/);
   if(match)return and(atom('生'+match[1],'人位',v),atom(match[2],'人位',v));
   fail('無法辨認人或時位「'+s+'」。');
  }
  const restriction=s.match(/^除(.+?)以外的(.+)$/);
  if(restriction){note('「除 A 以外的 B」限制被量化的 B；對 A 本身保持沉默。');return and(atom(restriction[2],sort,v),not(atom(restriction[1],sort,v)));}
  const mind=s.match(/^(?:(?:三界\.)?(欲界|無色界|色界)(?:繫)?)?(無覆無記|有覆無記|無覆|有覆|染污|善|不善|無記)?心$/);
  if(mind){
   const attrs=[pred('心',v)];
   if(mind[1])attrs.push(pred(realmIds[mind[1]],v));
   if(mind[2])attrs.push(atom(mind[2],'法',v));
   return conjunction(attrs);
  }
  const qual=s.match(/^(淨|無漏|有漏)(初|第一|第二|第三|第四)靜慮$/);
  if(qual)return and(atom(qual[2]+'靜慮',sort,v),pred(({淨:'等至.淨',無漏:'無漏',有漏:'有漏'})[qual[1]],v));
  fail('詞庫或句法尚未覆蓋「'+s+'」。保留原句，不猜測其意思。');
 }
 function list(s){
  const inclusive=/、|和|與/.test(s),alternative=s.includes('或');
  if(inclusive&&alternative)fail('並列中同時出現「和」與「或」。請拆開寫明範圍。');
  const terms=s.split(/、|和|與|或/);
  if(terms.some(t=>!t))fail('列舉缺少一項。');
  if(terms.length>1&&s.startsWith('除'))fail('例外項含並列，請先拆開寫明排除範圍。');
  return {terms,alternative};
 }
 function group(s,sort,v,role='range'){
  const {terms,alternative}=list(s);
  const join=role==='attributes'&&!alternative?conjunction:disjunction;
  return join(terms.map(t=>atom(t,sort,v)));
 }
 function checkNegatedList(s){
  if(list(s).terms.length>1)fail('否定的賓語含並列。請分句寫明是逐項排除，還是只否定兩項同時成立。');
 }
 function cls(left,right,op){
  if(left==='色界'&&right==='色界')fail('兩處「色界」可能各有所指，請分別寫出兩端的完整名稱。');
  const explicitLeft=realmValue(left),explicitRight=realmValue(right);
  if(explicitLeft||explicitRight||((left==='色界'||right==='色界')&&context.sejie==='realm')){
   function endpoint(s){
    if(s==='色界'){
     const meaning=choose(context,'sejie',[{value:'element',label:'十八界.色界（色境）'},{value:'realm',label:'三界.色界（界名）'}],'請指明「色界」所屬的分類。');
     if(meaning==='realm')return '三界.色界';
    }
    return realmValue(s);
   }
   const l=endpoint(left),r=endpoint(right);
   if(!l||!r)fail('界名與法類不能直接等同。若問一法繫屬何界，請寫「色界繫」；若問色境，請寫「十八界.色界」。');
   const equality={op:'realmEq',l,r};
   return op==='no'?not(equality):equality;
  }
  const sort=names.has(left)&&vocab[names.get(left)].sort==='人位'?'人位':'法';
  if(op==='no')checkNegatedList(right);
  if(op==='equal'&&[left,right].some(t=>list(t).terms.length>1))fail('並列的等同關係須先明寫是合類還是逐項比較。');
  const l=group(left,sort,'x'),r=group(right,sort,'x','attributes');
  if(op==='equal'){note('「等於」取兩種分類外延相同，保留雙向。');return all('x',sort,iff(l,r));}
  note('分類名稱作主詞時讀作泛稱，不由全稱句另行斷定有實例。');
  return all('x',sort,imp(l,op==='no'?not(r):r));
 }
 function has(s,thing,v='d',verb='成就'){
  const {terms,alternative}=list(thing);
  const items=terms.map(t=>some(v,'法',and(atom(t,'法',v),rel(verb,s,v))));
  return (alternative?disjunction:conjunction)(items);
 }
 function stateClaim(person,tail){
  const match=tail.match(/^(不成就|成就|只成就|唯成就|不現前|現前|不?得捨\.得|不?二修\.(?:得修|習修)|不得|得)(.+)$/);
  if(!match)fail('成就句缺少關係或賓語。');
  const [,verb,thing]=match;
  const explicit=verb.replace(/^不/,'');
  let relationship=relations[explicit]?explicit:'成就';
  if(explicit==='得'){
   const sense=choose(context,'gainSense',[{value:'acquisition',label:'得捨.得'},{value:'cultivation',label:'二修.得修'}],'請指明此處的「得」取取得義或得修義。');
   relationship=sense==='acquisition'?'得捨.得':'二修.得修';
  }
  const h=has('s',thing,'d',relationship);
  let result=h;
  if(verb.startsWith('不')){checkNegatedList(thing);result=not(h);}
  if(verb==='只成就'||verb==='唯成就'){
   const detail=thing.match(/^(有漏|無漏)(初|第二|第三|第四)靜慮$/);
   if(!detail)fail('「只」的比較集合未確定。請明寫要排除哪幾項。');
   const scope=choose(context,'only',[
    {value:'nature',label:'固定此靜慮，排除另一種漏性'},
    {value:'levels',label:'固定漏性，在四靜慮中排除其餘三地'},
    {value:'both',label:'兼用以上兩項限制'},
   ],'「只」沒有說明要排除哪些法。下列讀法只比較四靜慮；若另有範圍，請改寫原句。');
   const opposite=(detail[1]==='有漏'?'無漏':'有漏')+detail[2]+'靜慮';
   const outside=levels.filter(l=>l!==detail[2]).map(l=>not(has('s',detail[1]+l+'靜慮')));
   const exclusions=scope==='nature'?[not(has('s',opposite))]:scope==='levels'?outside:[not(has('s',opposite)),...outside];
   note('「只」按所選比較集合解讀，未排除的項保持未定。');
   result=and(h,...exclusions);
  }
  if(relationship==='成就')note('成就在同一人的同一時位判讀，不增加入定現前或初得的條件。');
  return all('s','人位',imp(group(person,'人位','s'),result));
 }
 return function parse(s){
  let m;
  // Whole-sentence operators scope over the entire recursively parsed statement.
  if(m=s.match(/^(?:並非所有|並非一切|並非每一個|不是所有)(.+)$/)){
   const claim=parse(m[1].replace(/^(.+?)都是/,'$1是'));
   if(claim.op!=='all')fail('「並非所有」必須修飾全稱命題。');
   note('否定整個全稱句，容有反例；不同於全稱否定。');return not(claim);
  }
  if(m=s.match(/^(?:所有的|所有|一切|每一個|每個|凡是|凡)(.+)$/)){
   const claim=parse(m[1]);if(claim.op!=='all')fail('全稱詞與所解析的句式不一致。');return claim;
  }
  if(m=s.match(/^(?:有些|有的|至少有一個)(.+?)(不是|是|屬於|非)(.+)$/)){
   const negative=['不是','非'].includes(m[2]);
   if(negative)checkNegatedList(m[3]);
   const rhs=group(m[3],'法','x','attributes');
   return some('x','法',and(group(m[1],'法','x'),negative?not(rhs):rhs));
  }
  if(m=s.match(/^沒有(.+?)(?:是|屬於)(.+)$/)){
   checkNegatedList(m[2]);return not(some('x','法',and(group(m[1],'法','x'),group(m[2],'法','x'))));
  }
  if(m=s.match(/^只有(.+?)才(?:是|屬於)(.+)$/)){
   note('「只有 A 才是 B」把 A 列為 B 的必要條件。');return cls(m[2],m[1],'yes');
  }
  if(m=s.match(/^只要(?:是)?(.+?)[，,]?(?:就|便)(?:是|屬於)(.+)$/))
   return cls(m[1],m[2],'yes');
  if(m=s.match(/^(只成就|唯成就|成就|不成就)(.+)$/)){
   const subject=choose(context,'subject',['有情','聖者','不還者','阿羅漢'].map(x=>({value:x,label:x})),'缺了主詞。請指定所談的人，或在原句補出主詞。');
   note('省略的主詞依所選語境補為「'+subject+'」。');return stateClaim(subject,s);
  }
  if(m=s.match(/^(.+?)[，,]?若成就(.+?)[，,](?:則|必|就)?(不成就|成就)(.+)$/)){
   note('條件句的前後件共用同一人位 s，各自的所得法可以不同。');
   if(m[3]==='不成就')checkNegatedList(m[4]);
   const end=has('s',m[4],'b');
   return all('s','人位',imp(and(group(m[1],'人位','s'),has('s',m[2],'a')),m[3]==='成就'?end:not(end)));
  }
  if(m=s.match(/^(.+?)既不是(.+?)(?:的)?[，,]?也不是(.+?)(?:的)?$/)){
   note('兩個否定都落在同一主詞上。');
   return all('x','法',imp(group(m[1],'法','x'),and(not(group(m[2],'法','x')),not(group(m[3],'法','x')))));
  }
  if(m=s.match(/^(.+?)(?:不等於|不等同於)(.+)$/))return not(cls(m[1],m[2],'equal'));
  if(m=s.match(/^(.+?)[，,]?(?:就)?(?:等於|等同於)(.+)$/))return cls(m[1],m[2],'equal');
  if(m=s.match(/^有(.+?)(?:而非|而不是|非)(.+)$/)){
   checkNegatedList(m[2]);
   note('「有 A 非 B」引入一個存在見證，同一個法滿足 A 與非 B。');
   return some('x','法',and(group(m[1],'法','x'),not(group(m[2],'法','x'))));
  }
  // Voice changes the order of the endpoints, never their meaning.
  let from,to,negative;
  if(m=s.match(/^(.+?)(?:是)?(不能|不可能|可以|能)(?:由|從)(.+?)無間(?:而)?生(?:的)?$/)){
   [,to,,from]=m;negative=['不能','不可能'].includes(m[2]);
  }else if(m=s.match(/^(.+?)(?:是)?(不能|不可能|可以|能)無間生(.+?)(?:的)?$/)){
   [,from,,to]=m;negative=['不能','不可能'].includes(m[2]);
  }
  if(from){
   const a=group(from,'法','a'),b=group(to,'法','b');
   if(!denotesMind(a)||!denotesMind(b))fail('無間生的兩端在這個片段中須明說心類。');
   note('前念是「'+from+'」，後念是「'+to+'」。能指此類到彼類容有一例；否定式排除所有這樣的念對。');
   const pair=some('a','法',some('b','法',and(a,b,rel('無間生','a','b'))));
   return negative?not(pair):pair;
  }
  if(m=s.match(/^(.+?)(能與|可與|不能與|不與)(.+?)相應$/)){
   const a=group(m[1],'法','a'),b=group(m[3],'法','b');
   const pair=some('a','法',some('b','法',and(a,b,rel('相應','a','b'))));
   note('「能與」讀作容有一對相應法，「不與」排除這種配對。');
   return m[2].startsWith('不')?not(pair):pair;
  }
  if(m=s.match(/^(.+?)通三性[：:](.+)$/)){
   const items=m[2].split(/[、，,]/);
   if(items.length!==3||new Set(items).size!==3||!items.every(i=>['善','不善','無記'].includes(i)))fail('「通三性」的列舉須與善、不善、無記三性吻合。');
   note('「通」展為三個各自存在的例，不把善與不善加在同一法例上。');
   return and(...items.map(k=>some('x','法',and(group(m[1],'法','x'),atom(k,'法','x')))));
  }
  if(m=s.match(/^(.+?)(?:只在|唯在)(.+?)(?:一部)?$/)){
   note('「只在」限制主詞所屬之部，沒有倒推出該部一切法皆屬主詞。');
   return cls(m[1],m[2],'yes');
  }
  if(m=s.match(/^(?:二修\.習修|習)(.+?)時[，,](?:如果|若)(二修\.得修|得捨\.得|得修|得)(.+?)[，,](?:也)?(?:一定會|必然|必|就會|則)(二修\.得修|得捨\.得|得修|得)(.+)$/)){
   const chosen=m[1].match(/^餘(有漏|無漏)$/);
   let practiced;
   if(chosen){
    const base=choose(context,'level',levelNames.map(x=>({value:x,label:x})),'「餘」排除哪一地？請從所在段落確定。');
    practiced=and(atom(chosen[1],'法','d'),not(atom(base,'法','d')));
    note('「餘」展開為此法不屬於'+base+'。');
   }else practiced=group(m[1],'法','d');
   const relation=m[2]==='得' || m[4]==='得' ? choose(context,'gainSense',[
    {value:'cultivation',label:'依本段術語取「得修」'},{value:'acquisition',label:'取一般的「得」'}],'這裡的「得」指得修，還是一般的得？') : 'cultivation';
   const action=word=>word==='得捨.得'?'得捨.得':word==='得'&&relation==='acquisition'?'得捨.得':'二修.得修';
   note('前後件共用同一人位。兩處所得依次取「'+action(m[2])+'」與「'+action(m[4])+'」。');
   const ongoing=some('d','法',and(practiced,rel('二修.習修','s','d')));
   return all('s','人位',imp(and(ongoing,has('s',m[3],'a',action(m[2]))),has('s',m[5],'b',action(m[4]))));
  }
  if(m=s.match(/^修(淨|無漏|有漏)(初靜慮|第二靜慮|第三靜慮|第四靜慮)?非(?:修)?(淨|無漏|有漏)(初靜慮|第二靜慮|第三靜慮|第四靜慮)?$/)){
   const level=m[2]||choose(context,'level',levelNames.map(x=>({value:x,label:x})),'「修」的賓語省去定地；請查上文所指。');
   const closure=choose(context,'closure',[{value:'case',label:'列舉的一種情形（開放條件）'},{value:'exists',label:'斷言至少有一個此類時位'}],'此短語是在列舉一格，還是在斷言該格有實例？');
   function practices(q,v){
    return some(v,'法',and(atom(q,'法',v),or(rel('二修.習修','s',v),rel('二修.得修','s',v))));
   }
   note('前項限定為'+level+'；後項'+(m[4]?'明寫定地':'承前省略同一定地')+'。「修」含習修或得修。否定覆蓋整個後項。');
   return bind(closure==='case'?'open':'some','s','人位',and(practices(m[1]+level,'a'),not(practices(m[3]+(m[4]||level),'b'))));
  }
  if(m=s.match(/^(.+?)(?:都)?(不是|是|屬於|非)(.+)$/))return cls(m[1],m[3],['非','不是'].includes(m[2])?'no':'yes');
  if(m=s.match(/^(.+?)(?:必然|必|都)?(不成就|只成就|唯成就|成就|不現前|現前|不?得捨\.得|不?二修\.(?:得修|習修)|不得|得)(.+)$/))return stateClaim(m[1],m[2]+m[3]);
  fail('這個句式尚不能完整解析；沒有生成部分公式。');
 };
}
function lookup(text,context){
 let id=realmValue(text)||names.get(text)||(Object.hasOwn(relations,text)?text:null);
 if(text==='色界'){
  const sense=choose(context,'sejie',[{value:'realm',label:'三界.色界（界名）'},{value:'element',label:'十八界.色界（色境）'}],'「色界」可以是界名，也可以是十八界中的色境。請選所問的分類。');
  id=sense==='realm'?'三界.色界':'十八界.色界';
 }else if(text==='得'){
  const options=[{value:'dharma',label:'心不相應行.得'},{value:'acquisition',label:'得捨.得'},{value:'cultivation',label:'二修.得修'}];
  const sense=choose(context,'gainSense',options,'這個「得」指一種法、於此時取得一法，還是修定語境中的得修？');
  id=options.find(o=>o.value===sense).label;
 }else if(text==='淨'){
  choose(context,'pureSense',[{value:'samapatti',label:'等至.淨'}],'請選「淨」所屬的分類。目前已收等至三分中的解釋。');
 }else if(text==='得修'||text==='習修')id='二修.'+text;
 return id?termInfo(id):null;
}
export function translate(text,context={}){
 const normalized=simple(String(text)).replace(/\s/g,'').replaceAll('．','.').replace(/[。；;.]$/,'');
 if(!normalized||normalized.length>600)return {status:'unsupported',message:'請輸入一條不超過 600 字的命題。'};
 const trace=[];
 try{
  const term=lookup(normalized,context);
  if(term)return {status:'term',term};
  const ast=reader(context,trace)(normalized);
  const symbols=inspect(ast);
  return {status:'parsed',ast,trace,symbols};
 }catch(e){
  if(!(e instanceof Issue))throw e;
  return {status:e.field?'needs-context':'unsupported',message:e.message,field:e.field,options:e.options||[]};
 }
}
