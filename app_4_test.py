import streamlit as st
import random
import time
import os
import numpy as np
from PIL import Image, ImageDraw
import io
import datetime
from fpdf import FPDF

# Důležité: Tento projekt vyžaduje následující knihovny.
# Ujistěte se, že je máte nainstalované ve virtuálním prostředí:
# pip install streamlit fpdf2 Pillow numpy

# --- DATA POHÁDEK (integrováno přímo do kódu) ---
fairytales_data = {
    "Dráček z mechového lesa": {
        "text": "V hlubokém Mechovém lese, kde mechy byly měkké jako polštáře a paprsky slunce tančily mezi větvemi, bydlel malý dráček jménem Šimonek. Nebyl to žádný děsivý drak – byl celý zelený, měl kulaté bříško, třepotavá křidélka a smál se, až se mu od pusy místo ohně valily bubliny! Každý den létal nízko nad zemí a počítal, kolik hub vyrostlo, kolik ptáčků zpívá a kolik mravenců si staví cestu. Bavilo ho to – byl totiž moc zvědavý. Jednoho dne ale pršelo tak silně, že se všechny cestičky v lese roztekly. Dráček nevěděl, kudy domů. Sedl si pod kapradinu a smutně foukal bublinky. V tu chvíli kolem šla víla Klárka. „Šimonku, proč jsi smutný?“ zeptala se. „Ztratil jsem se! Neumím spočítat, kolik kroků vede k mojí jeskyni,“ povzdychl si dráček. „To nevadí,“ usmála se víla. „Spočítáme to spolu! Každých deset kroků označíme kamínkem.“ A tak šli. Po každých deseti krocích položili kamínek. Po dvaceti krocích – dva kamínky. Po třiceti – tři. A hádejte co? Když položili šestý kamínek, dráček vykřikl radostí: „To je moje jeskyně!“ Od té doby Šimonek vždy, když prší, pomáhá ostatním zvířátkům v lese najít cestu pomocí počítání kroků a kamínků. A víte co? Už se nikdy neztratil. Naučil se, že počítání může zachránit den.",
        "moral": "Naučme se prožívat – nejen čísla, ale i cestu k přátelství.",
        "obrazek_path": "dracek.png"
    },
    "O Šípkové Růžence": {
        "text": "Kdysi dávno se v království narodila malá princezna Růženka. Král s královnou uspořádali velkou oslavu a pozvali víly z celého světa. Každá víla přinesla princezně dar – krásu, zpěv, radost… Ale jedna víla nebyla pozvaná. A protože se urazila, přišla nepozvána a zvolala: „Až jí bude šestnáct, píchne se o trn a usne na sto let!“ Všichni se polekali. Jedna hodná víla ale řekla: „Nebude to navždy – až ji někdo s čistým srdcem najde, probudí se.“ Král dal spálit všechny trny v království. Ale jeden zůstal schovaný – v koutě staré věže. A tak když bylo Růžence právě šestnáct let, šla se projít po zámku. Objevila schody, po kterých nikdy nešla… a v prachu věže objevila starý kolovrátek. Píchla se – a v tu ránu usnula. Usnulo i celé království. Stromy narostly, trny prorostly zámek. Les spal. Sto let… Až jednoho dne přišel mladý kluk jménem Matěj. Byl zvědavý a odvážný. Když viděl, že trny tvoří bludiště, začal počítat, kudy se dostane dál. Počítal kroky, hledal vzory, skládal cesty. Až došel ke dveřím… Uvnitř uviděl dívku, která spala jako anděl. Matěj ji tiše oslovil: „Jsi Růženka? Já jsem Matěj. Přinesl jsem ti světlo dnešního dne.“ V tu chvíli se Růženka probudila. Les se prosvítil. Trny se proměnily v květy.         A co dál? Matěj s Růženkou se stali přáteli – a každý den počítali květiny, ptáky i roky, které už nespí.",
        "moral": "Vždy existuje naděje, že i ten nejdelší spánek jednou skončí. Trpělivost přináší růže.",
        "obrazek_path": "ruzenka.png"
    },
    "Popelka": {
        "text": "V jedné daleké zemi žila dívka jménem Popelka. Její jméno vzniklo podle popela, který denně vymetala z krbu. I když žila v těžkých podmínkách – její nevlastní matka a dvě sestry jí stále poroučely – Popelka byla chytrá, trpělivá a měla dobré srdce. Když měla chvilku klidu, hrála si Popelka s kamínky a fazolemi. Nejenže z nich skládala obrazce, ale také počítala – sčítala je, řadila podle velikosti, třídila podle barvy. Matematika jí pomáhala zapomenout na starosti. Jednou večer přišel do vsi královský posel a rozhlásil: „Princ pořádá velký bál! Vybere si nevěstu. Každá dívka je zvána!“ Sestry se začaly chystat – počítaly šaty, boty a šperky: „Já mám 5 náušnic, ty máš 2... to je 7! Potřebujeme ještě 3 do deseti!“ Popelka tiše doufala, že půjde taky. Ale macecha jí jen řekla: „Ty nikam nejdeš, nemáš co na sebe – a nejdřív roztřiď 3 hrnce hrachu a čočky!“ Popelka si sedla a zoufala si – ale vtom se objevil bílý ptáček. „Pomohu ti. Ale musíš pomoci i ty mně – spočítej, kolik je 3x7.“ „To je dvacet jedna,“ řekla Popelka. Ptačí pomocníci zamávali křídly a všechna zrnka roztřídili. A vtom – zablesklo se. Na dvoře stála víla. „Zasloužíš si jít na ples. Pomohla jsi ostatním a umíš počítat!“ Mávla hůlkou – Popelka měla šaty poseté hvězdami, skleněné střevíčky a kočár z dýně. „Ale pamatuj – o půlnoci vše zmizí!“ Na plese Popelka okouzlila prince. Tancovali spolu a smáli se. Princ jí řekl: „Chci dívku, která má nejen krásné oči, ale i bystrý rozum. Položím ti hádanku: Když dnes máme 12 hostů, zítra přijde o 5 víc, kolik jich bude celkem?“ „Sedmnáct!“ usmála se Popelka. Princ byl ohromen. Ale hodiny odbily dvanáct, Popelka utekla… a ztratila jeden střevíček. Druhý den princ objížděl celé království a zkoušel skleněný střevíček dívce po dívce. V každém domě se zastavil, spočítal dívky a zapsal si, kolik pokusů už udělal. Až nakonec dorazil do posledního domu – kde našel tu pravou. Střevíček padl – a Popelka i princ věděli, že jejich životy se právě změnily.", 
        "moral": "Krása bez rozumu nevydrží – ale rozum a laskavost září navždy. Ten, kdo počítá, třídí, učí se a pomáhá ostatním, nakonec najde cestu i ze smutku.",
        "obrazek_path": "popelka.png"
    },
    "Počítání s lesní vílou Klárkou": {
        "text": "V hlubokém zeleném lese, kde slunce jemně prosvítá mezi listy, žila malá víla jménem Klárka. Každé ráno si oblékla svou růžovou květinovou sukýnku a vyletěla ze své šiškové chaloupky. Víla Klárka měla důležitý úkol – počítat vše, co se v lese děje. Kolik květin rozkvetlo, kolik ptáčků se narodilo, kolik veverek si schovalo oříšky. Jenže jednoho dne se všechno zamotalo! 🌸 „Dnes mi to nějak nejde,“ povzdychla si Klárka. „Pořád ztrácím počet!“ Vtom přišel dráček Šimonek. „Já ti pomůžu,“ řekl. A tak začali spolu: 🐞 „Támhle jsou 3 berušky,“ řekla Klárka. 🐦 „A tam 2 sýkorky, to je dohromady…?“ „5!“ vykřikl Šimonek radostně.       Pak potkali 4 veverky a každá měla 2 oříšky. „Kolik oříšků dohromady?“ zeptala se víla. Šimonek chvilku počítal… „8 oříšků!“ Celý den tak spolu počítali. Nakonec Klárka řekla: „Díky, dráčku. Učila jsem les počítat, ale dneska mě to naučil les a Ty!“     A od té doby chodili lesem spolu – víla s kouzelnou hůlkou a dráček s bystrou hlavičkou.",
        "moral": "Počítání může být zábava – zvlášť, když na to nejsi sám!",
        "obrazek_path": "vila.png"
    },
    "Sněhurka a sedm trpaslíků": {
        "text": "Kdysi dávno žila krásná dívka jménem Sněhurka. Měla vlasy černé jako noc, pleť bílou jako sníh a srdce laskavé jako jarní slunce. Jednoho  dne musela utéct do lesa, protože zlá královna jí nepřála. Běhala mezi stromy, až narazila na malý domeček. Zaklepala, ale nikdo  neodpověděl. Opatrně vešla – uvnitř bylo sedm židliček, sedm hrníčků a sedm postýlek. Sněhurka byla unavená, a tak si na chvilku lehla. A co se nestalo? Domeček patřil sedmi trpaslíkům – každý měl jinou barvu čepičky a jméno podle své nálady: Červený: Veselík, Oranžový: Popleta, Žlutý: Sluníčko, Zelený: Moudřík, Modrý: Plačtík, Fialový: Chrápálek, Bílý: Počtář. Když Sněhurku našli, vůbec se nezlobili. Byli rádi, že s nimi zůstane – vařila jim, uklízela a učila počítat a poznávat barvy. Jednoho dne však přišla zlá královna v přestrojení a nabídla Sněhurce červené jablko. Ale nebylo obyčejné – bylo začarované! Sněhurka si kousla… a usnula. Trpaslíci byli smutní. Ale jednoho dne projížděl kolem lesem princ, který uslyšel, co se stalo. Položil jablko na váhu a zjistil, že červená půlka vážila víc než zelená – a byla to ta kouzelná! Když jablko rozlomili a zakouzlili kouzelnou formuli (kterou naučil Počtář), Sněhurka se probudila! A víte co? Všichni se radovali, tancovali podle barev duhy – a každý den počítali nové příběhy.",
        "moral": "Někdy i malý trpaslík nebo obyčejné číslo může změnit velký příběh.",
        "obrazek_path": "snehurka.png"
    },
    "Červená Karkulka": {
        "text": "Karkulka šla navštívit svou babičku a nesla jí jídlo. V lese potkala vlka, který ji přelstil a dostal se k babičce dřív. Naštěstí je obě zachránil statečný myslivec.",
        "moral": "Poslouchej rady starších a nechoď sama do nebezpečných míst.",
        "obrazek_path": "karkulka.png"
    },
    "O Zlatovlásce": {
        "text": "Kdysi dávno žila v zámku princezna jménem Zlatovláska. Měla vlasy jako slunce – zlaté, lesklé a dlouhé až po paty. Ale nebyla jen krásná, byla i moudrá a laskavá. Každý den se procházela v zahradě a povídala si s ptáčky, květinami i malými broučky. Jednoho dne se v království objevil mladý kuchař Jiřík. Pracoval na zámku a zaslechl, že princezna je zakletá: „Zlatovláska nemůže být šťastná, dokud někdo nesplní tři kouzelné úkoly,“ řekl starý zahradník. Jiřík se rozhodl, že jí pomůže. Nebál se ničeho – ani draka, ani hádanek. První úkol: „Přines z řeky perlu, kterou tam upustil král,“ řekla zlatá rybka. Jiřík skočil do vody, početl bubliny – bylo jich deset – a na dně našel perlu. Druhý úkol: „Rozlušti hádanku,“ řekla moudrá sova. „Když mám dvě křídla a neumím létat – co jsem?“ Jiřík přemýšlel… „Dveře!“ zvolal. A sova pokývala hlavou. Třetí úkol: „Najdi srdce princezny,“ řekla čarovná květina. Jiřík šel do zahrady, kam Zlatovláska ráda chodila, a posadil se. „Tady je její srdce. Miluje květiny, zvířata a svět,“ řekl tiše. V tu chvíli se zakletí zlomilo. Zlatovláska se usmála a její zlaté vlasy zazářily ještě víc než dřív. A jak to dopadlo? Jiřík zůstal na zámku, vařil tu nejlepší polévku na světě – a srdce Zlatovlásky bylo šťastné.",
        "moral": "Pravá láska překoná všechny překážky.",
        "obrazek_path": "zlatovlaska.png"
    },
    "Sněhová královna": {
        "text": "Byli jednou dva kamarádi – Gerda a Kaj. Každý den si hráli na zahradě, běhali, sbírali květiny a dívali se na hvězdy. Jednoho zimního dne ale přiletěla Sněhová královna. Byla krásná, ale studená jako led. Mráz jí létal kolem vlasů a vločky jí sedaly na ramena. Když Kaj koukal z okna, jedna vločka mu spadla přímo do oka a malý střep ledu mu vklouzl do srdce. Od té chvíle už nebyl stejný. Přestal se smát, začal být zlý a odešel s královnou do jejího ledového zámku na dalekém severu. Gerda byla smutná, ale nevzdala se. Vydala se Kaje hledat. Šla lesem, kolem řeky, potkala vrány, lišku, babičku s květinami, a dokonce i prince a princeznu. Všichni jí pomáhali. Nakonec došla až ke zmrzlému zámku, kde seděl Kaj – úplně ztichlý a bledý. Už si ani nepamatoval, kdo je. Gerda ho obejmula. A slza z jejího oka dopadla na jeho srdce. Led roztál. Kaj si vzpomněl! Drželi se za ruce, sníh kolem začal tát a celý ledový zámek se proměnil v jaro. Spolu se vrátili domů – šťastní, že se nikdy nevzdali.", 
        "moral": "Přátelství a láska dokážou roztavit i ten největší led.",
        "obrazek_path": "snehova_kralovna.png"
    },
    "Perníková chaloupka": {
        "text": "Kdysi dávno, v malé chalupě na okraji lesa, žil dřevorubec se svými dvěma dětmi – Jeníčkem a Mařenkou. Byli chudí, ale vždy si všechno dělili, i to nejmenší. Otec jim jednoho dne dal poslední, co měl: malé červené jablíčko. „Děti moje, podělte se,“ řekl. „Ať vám vydrží co nejdéle.“ Mařenka se usmála a řekla: „Půlka pro tebe, půlka pro mě.“ Jeníček přikývl, ale místo aby jablíčko rozkrojili, jen si z něj oba malinko kousli – a pak ho schovali. A co bylo zvláštní – jablko zůstalo celé. Nezdálo se, že by ubylo. „To je zvláštní,“ řekla Mařenka. „Asi ví, že se dělíme.“ Druhého dne je macecha zavedla hluboko do lesa. Děti si chtěly zapamatovat cestu zpět, ale déšť smyl stopy a ptáci sezobali drobky. Bloudili dlouho. Když měli hlad, vytáhli jablíčko. „Už nám moc nezbylo,“ řekl Jeníček. „Ale vždyť se na něj podívej – pořád je celé,“ zašeptala Mařenka. A opravdu – jablíčko zůstávalo kulaté, lesklé a šťavnaté, přestože se z něj občas kousli. Možná proto, že se nikdy nehádali, kdo má víc. Pak spatřili chaloupku – z perníku, cukroví a bonbonů. Voněla jako sen. Ale děti věděly, že něco, co je až příliš sladké, může být nebezpečné. Ulomili si jen kousek – a i ten si rozdělili. A jablíčko, které nosili s sebou, pořád zůstávalo v kapse – celé, teplé, jako by dýchalo. Vtom se otevřely dveře. Vyšla stará žena, vlídná na pohled. Pozvala je dovnitř, ale brzy zavřela Jeníčka do klece a Mařenku nutila vařit. Děti však neztratily naději – měly pořád své jablíčko, které si dávaly večer potají k nosu, aby si připomněly domov. Mařenka vymyslela plán. Když čarodějnice chtěla Jeníčka upéct, poprosila ji, ať jí ukáže, jak se leze do pece. Když tam vlezla, Mařenka dvířka zavřela. Děti se osvobodily a našly truhlu se zlaťáky. Ale největší poklad měly u sebe: jablíčko, které zůstávalo celé – protože se o něj vždy dělily. Na cestě domů potkávaly hladové zvířátko, unaveného poutníka – každému nabídly kousek. A jablko? Zůstávalo kulaté. Možná proto, že ten, kdo dává s láskou, nikdy nepřijde o to, co má.",
        "moral": "Tvrdá práce a poctivost se vyplatí. Pevné základy jsou důležité.",
        "obrazek_path": "pernikova_chaloupka.png"
    },
    "O slepičce a kohoutkovi": {
        "text": "Byli jednou kohoutek Galois a slepička Poule. Celý den se spolu hrabali v prachu dvora a hledali dobrůtky. Byli nerozluční a nikdy se nehádali. Jednoho dne, když už slunce zapadalo a země voněla večerem, našel kohoutek v hlíně zlatavé semínko – krásné, kulaté, lesklé, jaké ještě nikdy neviděli. „Jé, semínko!“ zakokrhal kohoutek. „Našel jsem ho první, je moje!“ Slepička ale sklopila hlavičku a tiše řekla: „Copak jsme se nedomluvili, že vše dělíme napůl?“ Kohoutek se zarazil. Dlouze se na semínko zadíval, pak na slepičku, a zase na semínko. „Ale když jsem ho našel první...“ zamumlal. A v tu chvíli se zlaté semínko zatřpytilo a začalo mizet. Kohoutek zůstal stát s otevřeným zobákem – semínko bylo pryč! V trávě zašuměl vánek a zněl jako hlas: „Co je sobecké, ztrácí se. Co je sdílené, roste.“ Kohoutek se podíval na slepičku. Zahanbeně sklonil hlavu. „Příště budeme dělit, ať najde kdo chce,“ řekl. A od té doby si vše, co našli, spravedlivě rozdělovali – i když to bylo jen jedno jediné semínko.",
        "moral": "Co je nalezeno pro sebe, bývá snadno ztraceno. Co je sdíleno, má sílu růst.",
        "obrazek_path": "slepicka.png"
    },
}


# --- CSS pro zarovnání a stylování ---
st.markdown("""
<style>
/* Základní styly pro kontejner úkolů */
div.task-row {
    display: flex;
    align-items: center;
    gap: 1rem;
}

/* Sjednocení výšky prvků ve sloupci */
div.stTextInput > div > div {
    height: 38px !important;
}

/* Vizuální zarovnání obsahu uvnitř stTextInput */
div[data-testid="stTextInput"] > div > div > input {
    height: 100% !important;
}

/* Tlačítko Odeslat */
div.stButton > button {
    height: 38px !important;
    vertical-align: middle;
}

/* Zpětná vazba (success/error box) */
.stAlert {
    min-height: 38px !important;
    display: flex;
    align-items: center;
}

/* Další obecné styly */
.stForm {
    border: none !important;
    padding: 0 !important;
}
div[data-testid="stContainer"] {
    border: 1px solid #ddd;
    border-radius: 10px;
    padding: 20px;
    margin-bottom: 20px;
}
</style>
""", unsafe_allow_html=True)

# --- Inicializace stavu relace (Session State) ---
if "game_started" not in st.session_state:
    st.session_state.game_started = False
if "tasks_solved_for_reveal" not in st.session_state:
    st.session_state.tasks_solved_for_reveal = 0
if "score" not in st.session_state:
    st.session_state.score = 0
if "best_score" not in st.session_state:
    st.session_state.best_score = 0
if "best_time" not in st.session_state:
    st.session_state.best_time = float('inf')
if "start_time" not in st.session_state:
    st.session_state.start_time = None
if "end_time" not in st.session_state:
    st.session_state.end_time = None
if "current_task" not in st.session_state:
    st.session_state.current_task = None
if "last_selected_fairytale" not in st.session_state:
    st.session_state.last_selected_fairytale = None
if "last_selected_class" not in st.session_state:
    st.session_state.last_selected_class = None
if "revealed_tiles" not in st.session_state:
    st.session_state.revealed_tiles = [False] * 20
if "tile_coords" not in st.session_state:
    st.session_state.tile_coords = []
if "feedback_message" not in st.session_state:
    st.session_state.feedback_message = ""
if "feedback_type" not in st.session_state:
    st.session_state.feedback_type = ""
if "final_report" not in st.session_state:
    st.session_state.final_report = None
if "history" not in st.session_state:
    st.session_state.history = []
if "show_full_fairytale" not in st.session_state:
    st.session_state.show_full_fairytale = False
if "achievement_date" not in st.session_state:
    st.session_state.achievement_date = None
if "diploma_image_path" not in st.session_state:
    st.session_state.diploma_image_path = None


# Konfigurace hry
TASKS_TO_REVEAL = 20

# Mapování tříd na databázové úrovně
class_to_db_level = {
    "1. třída": "1. třída",
    "2. třída": "2. třída",
    "3. třída": "3. třída",
    "4. třída": "4. třída",
    "5. třída": "5. třída",
    "6. třída": "6. třída",
    "7. třída": "7. třída",
    "8. třída": "8. třída",
    "9. třída": "9. třída"
}

# Interní poznámky, které odpovídají generovaným úkolům
math_notes_by_level = {
    "1. třída": [
        "Sčítání a odčítání čísel v oboru do 20."
    ],
    "2. třída": [
        "Sčítání a odčítání do 100. Malá násobilka."
    ],
    "3. třída": [
        "Sčítání a odčítání v oboru do 1000. Dělení se zbytkem. **Výsledek zapiš ve tvaru `podíl zb. zbytek` (např. 5 zb. 2).**"
    ],
    "4. třída": [
        "Násobení a dělení s vícecifernými čísly. Odhady, zaokrouhlování."
    ],
    "5. třída": [
        "Sčítání, odčítání, násobení a dělení desetinných čísel. Zlomky (porovnávání, rozšiřování, krácení). **Zlomky zapiš ve tvaru `čitatel/jmenovatel` (např. 1/2).**"
    ],
    "6. třída": [
        "Základní operace s desetinnými čísly, zlomky (sčítání, odčítání) a jednoduché procenta. **Zlomky zapiš ve tvaru `čitatel/jmenovatel` (např. 1/2).**"
    ],
    "7. třída": [
        "Řešení lineárních rovnic typu $ax + b = c$, celá čísla, poměr, přímá a nepřímá úměrnost."
    ],
    "8. třída": [
        "Mocniny a odmocniny ($a^2, a^3, \\sqrt{a}$), Pythagorova věta, obvod a obsah kruhu."
    ],
    "9. třída": [
        "Řešení lineárních rovnic, jednoduché kvadratické rovnice ($x^2 = a$), základy statistiky (aritmetický průměr, medián) a finanční matematika (procenta, úroky)."
    ]
}

st.set_page_config(page_title="Pohádky s matematikou", layout="wide")
st.title("🌟 Pohádky s matematikou")

# --- Vylepšená Funkce pro generování matematických úkolů ---
def generate_math_problem(level):
    """Generuje náhodný matematický příklad na základě úrovně třídy."""
    problem = ""
    answer = None
    problem_type = "default"

    if level == "1. třída":
        num1 = random.randint(1, 10)
        num2 = random.randint(1, 10)
        operation = random.choice(["+", "-"])
        if operation == "-":
            num1, num2 = max(num1, num2), min(num1, num2)
        problem = f"${num1} {operation} {num2}$"
        answer = str(eval(f"{num1} {operation} {num2}"))
        problem_type = "basic"
    elif level == "2. třída":
        problem_type = random.choice(["add_sub", "multiplication"])
        if problem_type == "add_sub":
            num1 = random.randint(10, 99)
            num2 = random.randint(1, 99)
            operation = random.choice(["+", "-"])
            if operation == "-":
                num1, num2 = max(num1, num2), min(num1, num2)
            problem = f"${num1} {operation} {num2}$"
            answer = str(eval(f"{num1} {operation} {num2}"))
        else: # multiplication
            num1 = random.randint(2, 9)
            num2 = random.randint(2, 9)
            problem = f"${num1} \\cdot {num2}$"
            answer = str(num1 * num2)
        problem_type = "basic"
    elif level == "3. třída":
        problem_type = random.choice(["add_sub", "div_remainder"])
        if problem_type == "add_sub":
            num1 = random.randint(100, 999)
            num2 = random.randint(100, 999)
            operation = random.choice(["+", "-"])
            if operation == "-":
                num1, num2 = max(num1, num2), min(num1, num2)
            problem = f"${num1} {operation} {num2}$"
            answer = str(eval(f"{num1} {operation} {num2}"))
        else: # division with remainder
            divisor = random.randint(2, 9)
            quotient = random.randint(5, 50)
            remainder = random.randint(0, divisor - 1)
            dividend = divisor * quotient + remainder
            problem = f"${dividend} \\div {divisor}$"
            answer = f"{quotient} zb. {remainder}"
            problem_type = "div_remainder"
    elif level == "4. třída":
        num1 = random.randint(100, 999)
        num2 = random.randint(2, 20)
        operation = random.choice(["*", "/"])
        if operation == "*":
            problem = f"${num1} \\cdot {num2}$"
            answer = str(num1 * num2)
            problem_type = "basic"
        elif operation == "/":
            result = num1 * num2
            problem = f"${result} \\div {num2}$"
            answer = str(int(result / num2))
            problem_type = "basic"
    elif level == "5. třída":
        problem_type = random.choice(["decimal_add_sub", "decimal_mult_div", "fractions"])
        if problem_type == "decimal_add_sub":
            num1 = round(random.uniform(10, 100), 2)
            num2 = round(random.uniform(1, 10), 2)
            operation = random.choice(["+", "-"])
            if operation == "-":
                num1, num2 = max(num1, num2), min(num1, num2)
            problem = f"${num1} {operation} {num2}$"
            answer = str(round(eval(f"{num1} {operation} {num2}"), 2))
            problem_type = "decimal"
        elif problem_type == "decimal_mult_div":
            num1 = round(random.uniform(2, 20), 1)
            num2 = random.randint(2, 10)
            operation = random.choice(["*", "/"])
            if operation == "*":
                problem = f"${num1} \\cdot {num2}$"
                answer = str(round(num1 * num2, 1))
            else:
                result = num1 * num2
                problem = f"${result} \\div {num2}$"
                answer = str(round(result / num2, 1))
            problem_type = "decimal"
        else: # fractions
            num = random.randint(1, 5)
            den = random.randint(6, 10)
            problem = f"Zlomek $\\frac{{{num}}}{{{den}}}$ zjednoduš na základní tvar. (Pokud to nejde, napiš stejný zlomek.)"
            gcd = np.gcd(num, den)
            answer = f"{num // gcd}/{den // gcd}" # Updated to simple string
            problem_type = "fraction"
    elif level == "6. třída":
        problem_type = random.choice(["decimal", "fraction", "percentage"])
        if problem_type == "decimal":
            num1 = round(random.uniform(1, 20), 1)
            num2 = round(random.uniform(1, 10), 1)
            operation = random.choice(["+", "-"])
            problem = f"${num1} {operation} {num2}$"
            answer = str(round(eval(f"{num1} {operation} {num2}"), 1))
            problem_type = "decimal"
        elif problem_type == "fraction":
            num_a = random.randint(1, 5)
            den_a = random.randint(num_a + 1, 10)
            num_b = random.randint(1, 5)
            den_b = den_a
            
            problem_sub = f"Odčítání zlomků: $\\frac{{{max(num_a, num_b)}}}{{{den_a}}} - \\frac{{{min(num_a, num_b)}}}{{{den_b}}}$"
            answer_sub_num = max(num_a, num_b) - min(num_a, num_b)
            answer_sub = f"{answer_sub_num}/{den_a}" # Updated to simple string
            
            problem_add = f"Sčítání zlomků: $\\frac{{{num_a}}}{{{den_a}}} + \\frac{{{num_b}}}{{{den_b}}}$"
            answer_add_num = num_a + num_b
            gcd_add = np.gcd(answer_add_num, den_a)
            answer_add = f"{answer_add_num // gcd_add}/{den_a // gcd_add}" # Updated to simple string
            
            operation = random.choice(["add", "sub"])
            if operation == "sub":
                problem, answer = problem_sub, answer_sub
            else:
                problem, answer = problem_add, answer_add
                
            problem_type = "fraction"
            
        else: # percentage
            total = random.choice([100, 200, 500])
            percent = random.randint(5, 50)
            problem = f"Kolik je {percent}% z {total}?"
            answer = str(total * percent / 100)
            problem_type = "percentage"
    elif level == "7. třída":
        problem_type = random.choice(["linear_equation", "ratio", "proportion"])
        if problem_type == "linear_equation":
            a = random.randint(2, 5)
            x_val = random.randint(1, 10)
            b = random.randint(1, 10)
            c = a * x_val + b
            problem = f"${a}x + {b} = {c}$"
            answer = str(x_val)
            problem_type = "linear_equation"
        elif problem_type == "ratio":
            num1 = random.randint(2, 10)
            num2 = random.randint(num1 + 1, 20)
            problem = f"Zjednoduš poměr {num2} : {num1}"
            gcd = np.gcd(num1, num2)
            answer = f"{num2 // gcd} : {num1 // gcd}"
            problem_type = "ratio"
        else: # proportion
            a = random.randint(2, 5)
            b = random.randint(a + 1, 10)
            x = random.randint(1, 10)
            d = b * x / a
            problem = f"Vyřeš úměru: $\\frac{{{a}}}{{{b}}} = \\frac{{{x}}}{{?}}$"
            answer = str(d)
            problem_type = "proportion"
    elif level == "8. třída":
        problem_type = random.choice(["power", "root", "pythagorean", "circle"])
        if problem_type == "power":
            num = random.randint(2, 10)
            power = random.choice([2, 3])
            problem = f"${num}^{power}$"
            answer = str(num**power)
            problem_type = "power"
        elif problem_type == "root":
            num = random.randint(2, 10)
            problem = f"$\\sqrt{{{num**2}}}$"
            answer = str(num)
            problem_type = "root"
        elif problem_type == "pythagorean":
            a = 3
            b = 4
            c = 5
            side = random.choice(["a", "b", "c"])
            if side == "c":
                problem = f"Trojúhelník má odvěsny $a={a}$ a $b={b}$. Vypočítej délku přepony $c$."
                answer = str(c)
            elif side == "a":
                problem = f"Trojúhelník má přeponu $c={c}$ a odvěsnu $b={b}$. Vypočítej délku odvěsny $a$."
                answer = str(a)
            else:
                problem = f"Trojúhelník má přeponu $c={c}$ a odvěsnu $a={a}$. Vypočítej délku odvěsny $b$."
                answer = str(b)
            problem_type = "pythagorean"
        else: # circle
            radius = random.randint(3, 10)
            calculation_type = random.choice(["circumference", "area"])
            if calculation_type == "circumference":
                problem = f"Vypočítej obvod kruhu s poloměrem $r = {radius}$ (použij $\\pi \\approx 3.14$)."
                answer = str(round(2 * 3.14 * radius, 2))
            else:
                problem = f"Vypočítej obsah kruhu s poloměrem $r = {radius}$ (použij $\\pi \\approx 3.14$)."
                answer = str(round(3.14 * (radius**2), 2))
            problem_type = "circle"
    elif level == "9. třída":
        problem_type = random.choice(["linear", "quadratic", "statistics", "percentage_complex", "financial"])
        
        if problem_type == "linear":
            a = random.randint(2, 5)
            x_val = random.randint(1, 10)
            b = random.randint(1, 10)
            c = a * (x_val + b)
            problem = f"${a}(x + {b}) = {c}$"
            answer = str(x_val)
            problem_type = "linear"
        elif problem_type == "quadratic":
            perfect_squares = [4, 9, 16, 25, 36, 49, 64, 81, 100]
            square_val = random.choice(perfect_squares)
            sqrt_val = int(np.sqrt(square_val))
            problem = f"$x^2 = {square_val}$"
            answer = (str(sqrt_val), str(-sqrt_val))
            problem_type = "quadratic"
        elif problem_type == "statistics":
            numbers = sorted([random.randint(1, 20) for _ in range(random.randint(4, 6))])
            stat_type = random.choice(["mean", "median"])
            
            if stat_type == "mean":
                problem = f"Vypočítej průměr čísel: {', '.join(map(str, numbers))}"
                answer = str(round(np.mean(numbers), 2))
                problem_type = "statistics_mean"
            else: # median
                problem = f"Urči medián čísel: {', '.join(map(str, numbers))}"
                answer = str(np.median(numbers))
                problem_type = "statistics_median"
        elif problem_type == "percentage_complex":
            total = random.randint(100, 1000)
            percent = random.randint(10, 90)
            problem = f"Po zdražení o {percent}% stojí zboží {total} Kč. Kolik stálo původně?"
            answer = str(round(total / (1 + percent / 100), 2))
            problem_type = "percentage_complex"
        elif problem_type == "financial":
            principal = random.randint(1000, 10000)
            rate = random.randint(1, 5)
            years = random.randint(1, 3)
            interest = principal * rate / 100 * years
            problem = f"Jaký úrok získáš z {principal} Kč při roční úrokové míře {rate}% za {years} roky?"
            answer = str(interest)
            problem_type = "financial"

    return problem, answer, problem_type


def get_random_task(uroven, vyber_tridy):
    return generate_math_problem(vyber_tridy)

# --- Funkce pro získání souřadnic políček na obrázku ---
def get_tile_coordinates(image_path, rows, cols):
    """Načte obrázek a vypočítá souřadnice políček."""
    if not image_path or not os.path.exists(image_path):
        return []
    
    img = Image.open(image_path)
    width, height = img.size
    tile_width = width // cols
    tile_height = height // rows
    
    coords = []
    for r in range(rows):
        for c in range(cols):
            box = (c * tile_width, r * tile_height, (c + 1) * tile_width, (r + 1) * tile_height)
            coords.append(box)
            
    return coords

# --- VYLEPŠENÁ FUNKCE PRO GENEROVÁNÍ PDF DIPLOMU ---
def generate_diploma_pdf(username, score, time, fairytale_title, achievement_date, level, level_topic, image_path):
    """Generuje PDF diplom a vrací ho jako bajty."""
    pdf = FPDF(orientation='L', unit='mm', format='A4')
    pdf.add_page()
    page_width = pdf.w
    page_height = pdf.h

    try:
        pdf.add_font("DejaVuSans", "", "DejaVuSansCondensed.ttf", uni=True)
        pdf.add_font("DejaVuSans", "B", "DejaVuSansCondensed.ttf", uni=True)
    except RuntimeError:
        pdf.set_font("Arial", "", 24)
        st.warning("Upozornění: Font 'DejaVuSansCondensed.ttf' nebyl nalezen, na diplomu bude použito náhradní písmo.")

    if image_path and os.path.exists(image_path):
        original_img = Image.open(image_path)
        img_width, img_height = original_img.size

        img_with_alpha = original_img.convert("RGBA")
        background = Image.new("RGBA", img_with_alpha.size, (255, 255, 255, 255))
        alpha_value = 128
        img_with_alpha.putalpha(alpha_value)
        final_background_img = Image.alpha_composite(background, img_with_alpha)
        
        img_buffer = io.BytesIO()
        final_background_img.convert("RGB").save(img_buffer, format="JPEG")
        img_buffer.seek(0)

        aspect_ratio = img_width / img_height
        if page_width / page_height > aspect_ratio:
            bg_width = page_width
            bg_height = page_width / aspect_ratio
        else:
            bg_height = page_height
            bg_width = page_height * aspect_ratio

        y_pos = (page_height - bg_height) / 2
        if fairytale_title == "O Zlatovlásce": # Použít přesný název pohádky
            y_pos = 0
            
        pdf.image(img_buffer, x=(page_width - bg_width) / 2, y=y_pos, w=bg_width, h=bg_height)

    pdf.set_font("DejaVuSans", "", 36)
    pdf.set_xy(10, 30)
    pdf.cell(0, 10, 'Diplom', 0, 1, 'C')

    pdf.set_font("DejaVuSans", "", 18)
    pdf.set_xy(10, 50)
    pdf.cell(0, 10, f'Tento diplom získává za skvělý výkon ve hře Pohádky s matematikou', 0, 1, 'C')

    pdf.set_font("DejaVuSans", "B", 48)
    pdf.set_xy(10, 90)
    pdf.cell(0, 10, username, 0, 1, 'C')
    
    pdf.set_font("DejaVuSans", "", 16)
    pdf.set_xy(10, 120)
    pdf.cell(0, 10, f'za úspěšné vyřešení {score} úkolů v pohádce "{fairytale_title}"', 0, 1, 'C')
    pdf.set_xy(10, 130)
    pdf.cell(0, 10, f'v rekordním čase {time:.2f} sekund.', 0, 1, 'C')

    pdf.set_font("DejaVuSans", "", 12)
    pdf.set_xy(10, 160)
    pdf.cell(0, 10, f'Datum a čas: {achievement_date.strftime("%d.%m.%Y %H:%M")}', 0, 1, 'C')
    pdf.set_xy(10, 170)
    pdf.cell(0, 10, f'Úroveň: {level}', 0, 1, 'C')
    pdf.set_xy(10, 180)
    pdf.cell(0, 10, f'Téma: {level_topic}', 0, 1, 'C')

    return bytes(pdf.output(dest='S'))


# --- Veřejný obsah bočního panelu ---
st.sidebar.title("📚 Výběr pohádky")

fairytale_titles = list(fairytales_data.keys())
vyber = st.sidebar.selectbox("Vyberte pohádku", fairytale_titles)

tridy = ["1. třída", "2. třída", "3. třída", "4. třída", "5. třída", "6. třída", "7. třída", "8. třída", "9. třída"]
vyber_tridy = st.sidebar.selectbox("Vyberte úroveň", tridy)

st.sidebar.markdown("---")

# --- HLAVNÍ OBSAH STRÁNKY ---
if vyber:
    pohadka_data = fairytales_data.get(vyber)
    if pohadka_data:
        text = pohadka_data["text"]
        moral = pohadka_data["moral"]
        image_path_from_data = pohadka_data["obrazek_path"]
        
        base_name, _ = os.path.splitext(image_path_from_data)
        image_path = None
        
        if os.path.exists(os.path.join("obrazky", f"{base_name}.png")):
            image_path = os.path.join("obrazky", f"{base_name}.png")
        elif os.path.exists(os.path.join("obrazky", f"{base_name}.jpg")):
            image_path = os.path.join("obrazky", f"{base_name}.jpg")

        st.session_state.diploma_image_path = image_path
        
        if st.session_state.get("last_selected_fairytale") != vyber or st.session_state.get("last_selected_class") != vyber_tridy:
            st.session_state.current_task = None
            st.session_state.last_selected_fairytale = vyber
            st.session_state.last_selected_class = vyber_tridy
            st.session_state.feedback_message = ""
            st.session_state.feedback_type = ""
            st.session_state.tasks_solved_for_reveal = 0
            st.session_state.start_time = None
            st.session_state.end_time = None
            st.session_state.final_report = None
            st.session_state.history = []
            st.session_state.game_started = False
            st.session_state.revealed_tiles = [False] * 20
            st.session_state.tile_coords = get_tile_coordinates(image_path, 4, 5)
            st.session_state.show_full_fairytale = False
            st.session_state.best_score = 0
            st.session_state.best_time = float('inf')
            st.rerun()

        st.title(f"🧙 {vyber}")
        
        # --- ZMĚNA ZDE: Logika pro zobrazení náhledu textu ---
        if st.session_state.show_full_fairytale:
            st.markdown(text)
            if st.button("Skrýt celou pohádku"):
                st.session_state.show_full_fairytale = False
                st.rerun()
        else:
            # Vytvoření náhledu textu o určité délce
            preview_length = 300 # Počet znaků pro náhled
            if len(text) > preview_length:
                # Najít poslední mezeru v náhledu, aby se slovo nepřerušilo
                preview_text = text[:preview_length]
                last_space_index = preview_text.rfind(' ')
                if last_space_index != -1:
                    preview_text = preview_text[:last_space_index]
                st.markdown(preview_text + "...")
            else:
                # Pokud je text kratší než délka náhledu, zobrazit celý text bez "..."
                st.markdown(text)
            
            if st.button("Zobrazit celou pohádku"):
                st.session_state.show_full_fairytale = True
                st.rerun()
        # --- KONEC ZMĚNY ---

        st.divider()

        col_left, col_right = st.columns([1, 1])

        with col_left:
            st.markdown("### 📘 Matematická poznámka")
            db_level = class_to_db_level.get(vyber_tridy, "ZŠ")
            pozn_list = math_notes_by_level.get(db_level, ["Žádná poznámka pro tuto úroveň."])

            if pozn_list:
                with st.expander("📚 Zobrazit celou poznámku"):
                    for pozn in pozn_list:
                        st.markdown(pozn)
            else:
                st.info("Žádná poznámka pro tuto úroveň.")
            
            
            st.subheader("🧮 Úkoly")
            
            def start_new_game():
                st.session_state.start_time = time.time()
                st.session_state.tasks_solved_for_reveal = 0
                st.session_state.score = 0
                st.session_state.history = []
                st.session_state.feedback_message = ""
                st.session_state.feedback_type = ""
                st.session_state.game_started = True
                st.session_state.revealed_tiles = [False] * 20
                st.session_state.tile_coords = get_tile_coordinates(image_path, 4, 5)
                st.session_state.current_task = get_random_task(db_level, vyber_tridy)
                st.session_state.final_report = None
                st.session_state.achievement_date = None
                st.session_state.end_time = None
                st.rerun()

            if not st.session_state.game_started:
                st.info(f"Vyřešte {TASKS_TO_REVEAL} úkolů a odhalte obrázek! Stiskněte tlačítko 'Začít novou hru' a začněte počítat.")
                if st.button("Začít novou hru", key="start_new_game_initial"):
                    start_new_game()
                    
            else:
                if st.session_state.tasks_solved_for_reveal < TASKS_TO_REVEAL:
                    if st.session_state.current_task is None:
                        st.session_state.current_task = get_random_task(db_level, vyber_tridy)

                    question, correct_answer, problem_type = st.session_state.current_task
                    
                    with st.container():
                        col1, col2 = st.columns([4, 1])
                        with col1:
                            if problem_type in ["linear", "linear_equation"]:
                                 st.markdown(f"##### ✏️ Vyřeš rovnici: {question}, $x = ?$")
                            elif problem_type == "quadratic":
                                st.markdown(f"##### ✏️ Vyřeš rovnici: {question}, $x = ?$ (stačí jedna z možných odpovědí)")
                            elif problem_type.startswith("statistics"):
                                st.markdown(f"##### ✏️ {question}")
                            elif problem_type == "fraction":
                                st.markdown(f"##### ✏️ {question} **(Výsledek zapiš ve tvaru `čitatel/jmenovatel`.)**")
                            elif problem_type == "ratio":
                                st.markdown(f"##### ✏️ {question}")
                            elif problem_type == "proportion":
                                st.markdown(f"##### ✏️ {question}")
                            elif problem_type == "pythagorean":
                                st.markdown(f"##### ✏️ {question}")
                            elif problem_type == "circle":
                                st.markdown(f"##### ✏️ {question}")
                            elif problem_type.startswith("percentage"):
                                st.markdown(f"##### ✏️ {question}")
                            elif problem_type == "financial":
                                st.markdown(f"##### ✏️ {question}")
                            elif problem_type == "div_remainder":
                                st.markdown(f"##### ✏️ Vypočítej příklad: {question} = ? **(Výsledek zapiš ve tvaru `podíl zb. zbytek`.)**")
                            else:
                                st.markdown(f"##### ✏️ Vypočítej příklad: {question} $= ?$")
                        with col2:
                            st.markdown(f"🏅 **Skóre:** {st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL}")
                        
                        with st.form("math_task_form", clear_on_submit=True):
                            col_ans, col_btn, col_fb = st.columns(3)
                            
                            with col_ans:
                                user_answer = st.text_input("Tvoje odpověď:", key="math_answer_input", label_visibility="collapsed", placeholder="Sem napiš svou odpověď...")
                            
                            with col_btn:
                                submit_button = st.form_submit_button("Odeslat")
                            
                            with col_fb:
                                if st.session_state.get("feedback_message"):
                                    if st.session_state.feedback_type == "success":
                                        st.success(st.session_state.feedback_message)
                                    elif st.session_state.feedback_type == "error":
                                        st.error(st.session_state.feedback_message)
                                
                            if submit_button:
                                try:
                                    is_correct = False
                                    if isinstance(correct_answer, tuple):
                                        if user_answer.strip() in correct_answer:
                                            is_correct = True
                                    elif user_answer.strip() == correct_answer.strip():
                                        is_correct = True
                                    elif abs(float(user_answer.strip()) - float(correct_answer.strip())) < 1e-2:
                                        is_correct = True

                                    if is_correct:
                                        st.session_state.feedback_message = "Správně! 🎉"
                                        st.session_state.feedback_type = "success"
                                        st.session_state.tasks_solved_for_reveal += 1
                                        
                                        full_question = ""
                                        if problem_type in ["linear", "linear_equation"]:
                                            full_question = f"Vyřeš rovnici: {question}, $x = ?$"
                                        elif problem_type == "quadratic":
                                            full_question = f"Vyřeš rovnici: {question}, $x = ?$ (stačí jedna z možných odpovědí)"
                                        elif problem_type.startswith("statistics"):
                                            full_question = question
                                        elif problem_type == "fraction":
                                            full_question = f"{question} (Správný zápis: `čitatel/jmenovatel`)"
                                        elif problem_type == "ratio":
                                            full_question = question
                                        elif problem_type == "proportion":
                                            full_question = question
                                        elif problem_type == "pythagorean":
                                            full_question = question
                                        elif problem_type == "circle":
                                            full_question = question
                                        elif problem_type.startswith("percentage"):
                                            full_question = question
                                        elif problem_type == "financial":
                                            full_question = question
                                        elif problem_type == "div_remainder":
                                            full_question = f"Vypočítej příklad: {question} = ? (Správný zápis: `podíl zb. zbytek`)"
                                        else:
                                            full_question = f"Vypočítej příklad: {question} $= ?$"
                                        st.session_state.history.append((full_question, user_answer, correct_answer, "✅ správně"))
                                        
                                        unrevealed_tiles = [i for i, revealed in enumerate(st.session_state.revealed_tiles) if not revealed]
                                        if unrevealed_tiles:
                                            tile_to_reveal = random.choice(unrevealed_tiles)
                                            st.session_state.revealed_tiles[tile_to_reveal] = True
                                    else:
                                        correct_ans_display = correct_answer
                                        if isinstance(correct_answer, tuple):
                                            correct_ans_display = " nebo ".join(correct_answer)

                                        st.session_state.feedback_message = f"Nesprávně. ❌ Správná odpověď byla: {correct_ans_display}"
                                        st.session_state.feedback_type = "error"
                                        
                                        full_question = ""
                                        if problem_type in ["linear", "linear_equation"]:
                                            full_question = f"Vyřeš rovnici: {question}, $x = ?$"
                                        elif problem_type == "quadratic":
                                            full_question = f"Vyřeš rovnici: {question}, $x = ?$ (stačí jedna z možných odpovědí)"
                                        elif problem_type.startswith("statistics"):
                                            full_question = question
                                        elif problem_type == "fraction":
                                            full_question = f"{question} (Správný zápis: `čitatel/jmenovatel`)"
                                        elif problem_type == "ratio":
                                            full_question = question
                                        elif problem_type == "proportion":
                                            full_question = question
                                        elif problem_type == "pythagorean":
                                            full_question = question
                                        elif problem_type == "circle":
                                            full_question = question
                                        elif problem_type.startswith("percentage"):
                                            full_question = question
                                        elif problem_type == "financial":
                                            full_question = question
                                        elif problem_type == "div_remainder":
                                            full_question = f"Vypočítej příklad: {question} = ? (Správný zápis: `podíl zb. zbytek`)"
                                        else:
                                            full_question = f"Vypočítej příklad: {question} $= ?$"
                                        st.session_state.history.append((full_question, user_answer, correct_answer, "❌ špatně"))
                                except (ValueError, TypeError):
                                    st.session_state.feedback_message = "Prosím, zadej platné číslo."
                                    st.session_state.feedback_type = "error"
                                
                                st.session_state.current_task = None
                                st.rerun()

                    st.markdown("""
                    <script>
                    var input = document.querySelector('input[placeholder="Sem napiš svou odpověď..."]');
                    if (input) {
                        input.focus();
                    }
                    </script>
                    """, unsafe_allow_html=True)
                
                else:
                    st.snow()
                    if st.session_state.end_time is None:
                        st.session_state.end_time = time.time()
                        st.session_state.achievement_date = datetime.datetime.now()
                        total_time = st.session_state.end_time - st.session_state.start_time
                        correct_count = sum(1 for _, _, _, status in st.session_state.history if status == "✅ správně")
                        incorrect_count = len(st.session_state.history) - correct_count

                        is_new_best = False
                        if correct_count > st.session_state.best_score:
                            st.session_state.best_score = correct_count
                            is_new_best = True
                        if total_time < st.session_state.best_time:
                            st.session_state.best_time = total_time
                            is_new_best = True

                        report_text = f"#### ✨ Gratuluji k odhalení celého obrázku!\n\n"
                        report_text += f"Zde je tvá výsledková listina:\n"
                        report_text += f"- Správně vyřešených úkolů: **{correct_count}**\n"
                        report_text += f"- Nesprávně vyřešených úkolů: **{incorrect_count}**\n"
                        report_text += f"- Čas na vyřešení 20 úkolů: **{total_time:.2f}** sekund\n\n"
                        report_text += f"Skvělý výkon! Zkus vyřešit úkoly znovu a překonat svůj čas."

                        if is_new_best:
                            report_text += "\n\n**🏆 Nový osobní rekord!**"

                        st.session_state.final_report = report_text
                        st.session_state.score = st.session_state.tasks_solved_for_reveal
                    st.success("Vyřešil/a jsi všechny úkoly! Gratuluji!")

            if st.session_state.game_started:
                if st.checkbox("📜 Zobrazit historii odpovědí", key="history_math"):
                    st.markdown("---")
                    st.subheader("Historie řešení")
                    for i, item in enumerate(reversed(st.session_state.history), 1):
                        if len(item) == 4:
                            q, a_user, a_correct, v = item
                            display_correct_ans = a_correct
                            if isinstance(a_correct, tuple):
                                display_correct_ans = " nebo ".join(a_correct)

                            if v == "✅ správně":
                                st.markdown(f"{i}. {q} -> **{a_user}** {v}")
                            else:
                                st.markdown(f"{i}. {q} -> {a_user} (správná odpověď byla: **{display_correct_ans}**) {v}")
            
            if st.session_state.final_report:
                st.subheader("🏆 Výsledková listina")
                st.info(st.session_state.final_report)

                  
                
                st.subheader("📜 Vytvořit diplom")
                
                st.markdown(f"Tvůj nejlepší výsledek v pohádce **'{vyber}'** na úrovni **'{vyber_tridy}'** je:\n\n"
                            f"**{st.session_state.best_score}** správně zodpovězených úkolů v čase **{st.session_state.best_time:.2f}** sekund.")

                diploma_name = st.text_input("Jméno na diplom:", value="", help="Zadejte jméno, které chcete mít na diplomu.")
                
                if diploma_name and st.session_state.best_score > 0 and st.session_state.achievement_date:
                    level_topic = math_notes_by_level.get(class_to_db_level.get(vyber_tridy), ["Téma není k dispozici."])[0]
                    pdf_data = generate_diploma_pdf(diploma_name, st.session_state.best_score, st.session_state.best_time, vyber, st.session_state.achievement_date, vyber_tridy, level_topic, st.session_state.diploma_image_path)
                    
                    if pdf_data:
                        st.download_button(
                            label="Stáhnout diplom v PDF",
                            data=pdf_data,
                            file_name=f"diplom_{diploma_name}.pdf",
                            mime="application/pdf",
                            help="Stáhne diplom ve formátu PDF.",
                            key="download_diploma_btn"
                        )

           
                                
            if st.session_state.game_started and st.session_state.tasks_solved_for_reveal >= TASKS_TO_REVEAL:
                if st.button("Začít novou hru", key="restart_game_final"):
                    start_new_game()


        with col_right:
            st.subheader("🖼️ Obrázek")
            if image_path:
                if st.session_state.tasks_solved_for_reveal >= TASKS_TO_REVEAL:
                    st.image(image_path, use_container_width=True, caption=f"Gratuluji, obrázek je kompletní! ({st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL})")
                else:
                    img = Image.open(image_path)
                    draw = ImageDraw.Draw(img)
                    
                    if not st.session_state.game_started:
                        tiles_to_cover_indices = range(TASKS_TO_REVEAL)
                        caption_text = "Začněte novou hru a odhalte obrázek!"
                    else:
                        tiles_to_cover_indices = [i for i, revealed in enumerate(st.session_state.revealed_tiles) if not revealed]
                        caption_text = f"Odhalených {st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL} políček"

                    for i in tiles_to_cover_indices:
                        if st.session_state.tile_coords and i < len(st.session_state.tile_coords):
                            coords = st.session_state.tile_coords[i]
                            draw.rectangle(coords, fill="black")
                    
                    buf = io.BytesIO()
                    img.save(buf, format="PNG")
                    st.image(buf, use_container_width=True, caption=caption_text)
            
            elif not image_path:
                st.warning("Obrázek k zobrazení nebyl nalezen.")
            else:
                st.image("https://placehold.co/600x400/E0E0E0/000000?text=Obrázek+chybí", use_container_width=True)


        st.divider()

        st.subheader("⭐ Mravní ponaučení")
        if moral:
            st.info(moral)
        else:
            st.warning("Ponaučení není zadáno.")
            
else:
    st.warning("Nebyla vybrána žádná pohádka.")








