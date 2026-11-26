import {translate} from '../docs/translate/grammar.mjs';
import {render,leanFile,backtranslate} from '../docs/translate/logic.mjs';
import {cases} from '../docs/translate/cases.mjs';

const [cmd,...args]=process.argv.slice(2);
if(cmd==='--demo-lean'){
 const roots=cases.map(c=>{
  const r=translate(c.text,c.defaults);
  if(r.status!=='parsed')throw Error(c.id+' '+r.message);
  return r.ast;
 });
 process.stdout.write(leanFile(roots));
}else if(cmd){
 const context=Object.fromEntries(args.filter(a=>a.includes('=')).map(a=>a.split('=')));
 const r=translate(cmd,context);
 if(r.status==='parsed' && args.includes('--lean'))process.stdout.write(leanFile([r.ast]));
 else console.log(JSON.stringify(r.status==='parsed'?{...r,formula:render(r.ast),chinese:backtranslate(r.ast)}:r,null,2));
 if(r.status!=='parsed')process.exitCode=2;
}else{
 console.log('node tools/translate.mjs "自然語句" [--lean] [level=初靜慮 closure=case] [only=nature|levels|both]');
}
