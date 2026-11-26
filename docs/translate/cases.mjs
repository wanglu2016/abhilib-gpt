// Source specimens contain text and editorial context only. The parser never imports this file.
export const edition = 'https://raw.githubusercontent.com/wanglu2016/abhidharma/88bc5fbba7f266a66c23c92c1f7a6922cece8af2/books/'+encodeURIComponent('俱舍九題電子書.pdf');
export const cases = [
 {id:'01',chapter:'一',page:24,title:'異熟果的兩個否定',text:'異熟果既不是善的，也不是不善的。',voice:'作者論述中的分句',context:'上文在問善法可否作異熟果。本分句給出排除的理由。',check:'同一異熟果受到兩個否定；句中沒有斷言所有無記法都是異熟果。'},
 {id:'02',chapter:'二',page:49,title:'十八界與十二處的「色」',text:'十八界中的色界，就等於十二處中的色處。',voice:'作者陳述',context:'作者先分辨色境與三界中的色界，再比較兩種分類。',check:'看兩邊是否指向法的同一批成員；刪去「十八界中的」，應當出現詞義選擇。'},
 {id:'03',chapter:'二',page:53,title:'業道與業',text:'有業道非業',voice:'作者所引《婆沙》句內節錄',context:'接下來以後三業道作例。原文書頁有引號，這裡取其中待譯分句。',check:'看「有」是否引入一個例，而非把整類業道排除於業之外。'},
 {id:'04',chapter:'三',page:63,title:'兩類心能否前後相生',text:'欲界善心可以無間生色界善心',voice:'作者陳述中的分句',context:'此處說入有漏定。欲、色表繫界，前後是同一相續的兩念。',check:'「可以」只承諾這種念對可有；請檢查哪一念在先。'},
 {id:'05',chapter:'三',page:75,title:'把後念放在句首',text:'學心不能由無學心無間而生。',voice:'作者結論，節去句首「因此」',context:'十二心相生。作者問學心從幾心生，並討論阿羅漢退。',check:'公式中被禁止的順序，應是無學心在前、學心在後。'},
 {id:'06',chapter:'四',page:85,title:'「除通果心以外」排除什麼',text:'上界有情不成就除通果心以外的欲界心。',voice:'作者陳述',context:'上界指色、無色二界；此段前文分別談欲界通果心的捨與不捨。',check:'例外項從否定範圍移出。是否錯把它反推成上界人人成就欲界通果心？'},
 {id:'07',chapter:'六',page:105,title:'一根通三性',text:'苦根通三性：善、不善、無記。',voice:'作者結論，節去句首「因此」',context:'二十二根的四門分別中，這一句只取善等三性來判攝苦根。',check:'三種可能要分別有例，不能要求同一苦根同時具三性。'},
 {id:'08',chapter:'七',page:129,title:'兩種見與所斷部別',text:'身見、邊見只在見苦所斷一部',voice:'作者陳述中的分句',context:'作者在五部裡分別愛結、見結；「只在」談法的所斷部別。',check:'應覆蓋兩種見，保留包含方向，不推得「見苦所斷皆是二見」。'},
 {id:'09',chapter:'八',page:140,title:'習餘無漏時的得修',text:'習餘無漏時，如果得淨初靜慮，也一定會得無漏初靜慮。',voice:'作者陳述，節去句首「因為」',context:'第 139 頁把「餘」界定為非初靜慮；第 140 頁在習修、得修的四句中解釋一個空格。第 141 頁明說此段的「得」指得修。',defaults:{level:'初靜慮',gainSense:'cultivation'},check:'三項條件須落在同一人位。「餘」排除初靜慮；兩處「得」是否都保留得修義？'},
 {id:'10',chapter:'九',page:189,title:'同一人位的條件句',text:'生欲界，若成就無漏律儀，必成就靜慮律儀。',voice:'作者陳述',context:'討論不同生地的有情所成就的律儀。此句保留生欲界的限制。',check:'前後件須是同一人的同一時位；兩處所成就的法各自量化。'}
];

export const fragment = {id:'09b',chapter:'八',page:139,title:'一個省去定地的分句',text:'修淨非無漏。',voice:'四句的第一格，節去序號「一、」',context:'第 138 頁設定初靜慮，第 139 頁明說淨、無漏皆承前指初靜慮，並區分習修、得修。列出一格本身尚未承諾有例。',defaults:{level:'初靜慮',closure:'case'},check:'檢查補入的定地、否定範圍，以及輸出是對人位的條件還是存在斷言。可清除上下文再試。'};
