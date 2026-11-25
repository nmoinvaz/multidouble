import ExpansionBounds.Trig2.Data

/-!
# Theorem 35 at `n = 2` and `p = 53`: Horner's runs of the buckets 0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 13, 18, 28

Each run is checked by the kernel in pieces of at most 2 steps, from the state before a piece to the state after
it, and then `TrigTab.Ok` and, for the tangent, `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

def trig2_s0_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1196468123029483943208274081848508659365297614962798436525931, 389),
    [(500971590687981412920915483420441355374563860916659230861083, 282),
     (1001943181375963078555465349204144862233665475512184430765535, 336)])

def trig2_s0_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((9602896459180387223753925958846970007939581374091725910399, 364),
    [(1160392569983453040792769933826037709496150155971254030577361, 265),
     (580196284991726689826028134871931729889478082058780209814979, 317)])

def trig2_s0_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1279947247599824543459984882170274477340094530557262679357991, 354),
    [(317914559845777883109042116727393622047639997248672680586689, 246),
     (1271658239383111889981941000249902844355533851540951791199765, 301)])

def trig2_s0_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1415660121771452026343363855939160746136758312935903564608791, 338),
    [(1108354471337331096386015973356251490104868333242883859401335, 232),
     (4329509653661450898724927060043910522423221986823157228291, 277)])

def trig2_s0_10 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((735553501926904217869709516857293598740994204744411836889447, 323),
    [(290212443971994043182129426617328665104270398974027228725395, 216),
     (145106221985997063777387972611389206303316963869583724599801, 268)])

def trig2_s0_12 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((908540570800586890464283225754340269101738075703844464837887, 312),
    [(214258405901198727193056490744822905325327279276707687712289, 204),
     (857033623604795113760648044570826717357324391948873982506577, 259)])

def trig2_s0_13 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((360056964160719347325461716737814317734684335847253655244875, 306),
    [(1071292029505993635965282453724123658954208603614299396962449, 202),
     (267823007376498485161356001653669342413638873014066785602711, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_s0_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 0 14 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 14) = dySt trig2_s0_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s0_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 0 14 2 2 (dySt trig2_s0_2) = dySt trig2_s0_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s0_4_6 :
    trig2Tab.run sinCQ trig2Tab.FsQ 0 14 4 2 (dySt trig2_s0_4) = dySt trig2_s0_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s0_6_8 :
    trig2Tab.run sinCQ trig2Tab.FsQ 0 14 6 2 (dySt trig2_s0_6) = dySt trig2_s0_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s0_8_10 :
    trig2Tab.run sinCQ trig2Tab.FsQ 0 14 8 2 (dySt trig2_s0_8) = dySt trig2_s0_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s0_10_12 :
    trig2Tab.run sinCQ trig2Tab.FsQ 0 14 10 2 (dySt trig2_s0_10) = dySt trig2_s0_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s0_12_13 :
    trig2Tab.run sinCQ trig2Tab.FsQ 0 14 12 1 (dySt trig2_s0_12) = dySt trig2_s0_13 := by
  decide +kernel

theorem trig2_s0 : trig2Tab.run sinCQ trig2Tab.FsQ 0 14 0 13 (trig2Tab.init sinCQ trig2Tab.FsQ 14) =
    dySt trig2_s0_13 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 0 14 _ 2 11 trig2_s0_0_2
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 0 14 _ 2 9 trig2_s0_2_4
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 0 14 _ 2 7 trig2_s0_4_6
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 0 14 _ 2 5 trig2_s0_6_8
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 0 14 _ 2 3 trig2_s0_8_10
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 0 14 _ 2 1 trig2_s0_10_12
    (trig2_s0_12_13))))))

def trig2_c0_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((424359618481328000136758951517426399715421822709209372293799, 383),
    [(782768110449970957688930442844437939862612057072154441877835, 278),
     (782768110449971149558489537760403873785647962517510517700269, 331)])

def trig2_c0_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((193200420077733032421197160098588076054954499681754355357717, 364),
    [(1523015248103282116040510538146662470242783633705309374853289, 261),
     (380753812025820615002468811960178330187795886675684770084473, 312)])

def trig2_c0_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((680545587178802813237647260417477620802440883444234378163833, 349),
    [(1351136879344556003213428996091415487270876787786984076721611, 244),
     (675568439672278158133619880197158029567533913664302308110583, 296)])

def trig2_c0_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((484719166376573122790952051666670824057649676543539435781981, 333),
    [(450269003980790757906818989175975032058535355229165427599265, 227),
     (900538007961581768530918586930755093060470409711214741038825, 281)])

def trig2_c0_10 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1333877784884566666513879011023881135067315803102154508681999, 321),
    [(652977998936986597159791209888982711503733379077172527354097, 214),
     (326488999468493371855089272218544298907529729727382658352255, 266)])

def trig2_c0_12 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1408170093181585442371256891648709213781883357540417159175587, 310),
    [(66955751844124602247830153357757687018309379659773228356067, 200),
     (535646014752996969099899963449195734228483651074244713009225, 256)])

def trig2_c0_13 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((940365878052310212358667535238362117609456255133063816206329, 306),
    [(803469022129495226973961840293086476503876281023256894597147, 200),
     (401734511064747707275506863737085474430900769764098101561679, 252)])

set_option maxHeartbeats 4000000 in
theorem trig2_c0_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 0 14 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 14) = dySt trig2_c0_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c0_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 0 14 2 2 (dySt trig2_c0_2) = dySt trig2_c0_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c0_4_6 :
    trig2Tab.run cosCQ trig2Tab.FcQ 0 14 4 2 (dySt trig2_c0_4) = dySt trig2_c0_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c0_6_8 :
    trig2Tab.run cosCQ trig2Tab.FcQ 0 14 6 2 (dySt trig2_c0_6) = dySt trig2_c0_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c0_8_10 :
    trig2Tab.run cosCQ trig2Tab.FcQ 0 14 8 2 (dySt trig2_c0_8) = dySt trig2_c0_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c0_10_12 :
    trig2Tab.run cosCQ trig2Tab.FcQ 0 14 10 2 (dySt trig2_c0_10) = dySt trig2_c0_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c0_12_13 :
    trig2Tab.run cosCQ trig2Tab.FcQ 0 14 12 1 (dySt trig2_c0_12) = dySt trig2_c0_13 := by
  decide +kernel

theorem trig2_c0 : trig2Tab.run cosCQ trig2Tab.FcQ 0 14 0 13 (trig2Tab.init cosCQ trig2Tab.FcQ 14) =
    dySt trig2_c0_13 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 0 14 _ 2 11 trig2_c0_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 0 14 _ 2 9 trig2_c0_2_4
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 0 14 _ 2 7 trig2_c0_4_6
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 0 14 _ 2 5 trig2_c0_6_8
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 0 14 _ 2 3 trig2_c0_8_10
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 0 14 _ 2 1 trig2_c0_10_12
    (trig2_c0_12_13))))))

set_option maxHeartbeats 4000000 in
theorem trig2_ok0 : trig2Tab.Ok trig2C 0 15 15 (dySt trig2_s0_13) (dySt trig2_c0_13) := by
  decide +kernel

theorem trig2_g0 : trig2Tab.Group trig2C (0, 15, 15) :=
  ⟨_, _, trig2_s0, trig2_c0, trig2_ok0⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok0 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 0 15 15 (dySt trig2_s0_13) (dySt trig2_c0_13) := by
  decide +kernel

theorem tan2_g0 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (0, 15, 15) :=
  ⟨_, _, trig2_s0, trig2_c0, tan2_ok0⟩

def trig2_s1_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((613287160022860465491077042971600952295660989942650108205493, 370),
    [(1160392569983453040792769933826037656752386241737945181339403, 265),
     (290098142495863344866310988098267758312586122940421256975551, 316)])

def trig2_s1_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((318910777323506236946364471475708676172767860524456050026309, 352),
    [(635829119691555766218084233454787200754802370928098674917079, 247),
     (158957279922888986209880463696827753998915215759307029938397, 298)])

def trig2_s1_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1409831088656714261000767245510682018230344028492021433017925, 338),
    [(277088617834332774096503993339062842630817944620284903837437, 230),
     (1108354471337331429643638737530888889412055038855462950313899, 285)])

def trig2_s1_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1459165463813750190808562959423577618371635100383167329609029, 324),
    [(1160849775887976172728517706469314417783111239264917793349097, 218),
     (145106221985997063669928566764450590339444888201573754330897, 268)])

def trig2_s1_10 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((442893474304812969524027207750727085939578059901676817009105, 311),
    [(214258405901198727193056490744822789073257941715825405882753, 204),
     (857033623604795112098385360375995005813429490483164340126573, 259)])

def trig2_s1_11 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((344934439673042023694563303054016292798308192221315191122231, 306),
    [(1071292029505993635965282453724122428917081263427920593664027, 202),
     (1071292029505993936281984460603244117461432079911657745531659, 255)])

set_option maxHeartbeats 4000000 in
theorem trig2_s1_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 1 12 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 12) = dySt trig2_s1_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s1_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 1 12 2 2 (dySt trig2_s1_2) = dySt trig2_s1_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s1_4_6 :
    trig2Tab.run sinCQ trig2Tab.FsQ 1 12 4 2 (dySt trig2_s1_4) = dySt trig2_s1_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s1_6_8 :
    trig2Tab.run sinCQ trig2Tab.FsQ 1 12 6 2 (dySt trig2_s1_6) = dySt trig2_s1_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s1_8_10 :
    trig2Tab.run sinCQ trig2Tab.FsQ 1 12 8 2 (dySt trig2_s1_8) = dySt trig2_s1_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s1_10_11 :
    trig2Tab.run sinCQ trig2Tab.FsQ 1 12 10 1 (dySt trig2_s1_10) = dySt trig2_s1_11 := by
  decide +kernel

theorem trig2_s1 : trig2Tab.run sinCQ trig2Tab.FsQ 1 12 0 11 (trig2Tab.init sinCQ trig2Tab.FsQ 12) =
    dySt trig2_s1_11 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 1 12 _ 2 9 trig2_s1_0_2
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 1 12 _ 2 7 trig2_s1_2_4
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 1 12 _ 2 5 trig2_s1_4_6
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 1 12 _ 2 3 trig2_s1_6_8
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 1 12 _ 2 1 trig2_s1_8_10
    (trig2_s1_10_11)))))

def trig2_c1_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((545211674454948925329310743048873247108152345942887356006383, 374),
    [(843921869078874938758378133691667995239237154537755415472281, 269),
     (210980467269718800319160120881805366712442608206987203794517, 320)])

def trig2_c1_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((700682319824746438774900303443568584851996935454542462735225, 357),
    [(1130362879451654695498816415030738296781961287720509646817097, 252),
     (282590719862913758213144045021385744256090299890356937570575, 303)])

def trig2_c1_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1332372937341359147118565293354837098380354445279138389118525, 342),
    [(633345412192760626506294841917851960700645240933302817827583, 235),
     (1266690824385521557376892003932818299301805748004690389087491, 289)])

def trig2_c1_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((127912223449241800216592934052809714531337007160669885694875, 324),
    [(928679820710380938182814165175451689674373842443945095994315, 221),
     (232169955177595306219685997376643525945381278784312536104469, 272)])

def trig2_c1_10 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((637058286613936400325545681869362033961783879120972839650277, 314),
    [(571355749069863272514817308652862864021365853100187482541157, 208),
     (1142711498139726843505640195099784526951131670867721414028623, 262)])

def trig2_c1_12 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((858305084610452999560305305453794139331776164133754256315305, 306),
    [(401734511064747613486980920146542429738811562131908011874407, 199),
     (803469022129495409096714294959879304140553292820927457635857, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_c1_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 1 13 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 13) = dySt trig2_c1_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c1_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 1 13 2 2 (dySt trig2_c1_2) = dySt trig2_c1_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c1_4_6 :
    trig2Tab.run cosCQ trig2Tab.FcQ 1 13 4 2 (dySt trig2_c1_4) = dySt trig2_c1_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c1_6_8 :
    trig2Tab.run cosCQ trig2Tab.FcQ 1 13 6 2 (dySt trig2_c1_6) = dySt trig2_c1_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c1_8_10 :
    trig2Tab.run cosCQ trig2Tab.FcQ 1 13 8 2 (dySt trig2_c1_8) = dySt trig2_c1_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c1_10_12 :
    trig2Tab.run cosCQ trig2Tab.FcQ 1 13 10 2 (dySt trig2_c1_10) = dySt trig2_c1_12 := by
  decide +kernel

theorem trig2_c1 : trig2Tab.run cosCQ trig2Tab.FcQ 1 13 0 12 (trig2Tab.init cosCQ trig2Tab.FcQ 13) =
    dySt trig2_c1_12 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 1 13 _ 2 10 trig2_c1_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 1 13 _ 2 8 trig2_c1_2_4
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 1 13 _ 2 6 trig2_c1_4_6
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 1 13 _ 2 4 trig2_c1_6_8
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 1 13 _ 2 2 trig2_c1_8_10
    (trig2_c1_10_12)))))

set_option maxHeartbeats 4000000 in
theorem trig2_ok1 : trig2Tab.Ok trig2C 1 13 14 (dySt trig2_s1_11) (dySt trig2_c1_12) := by
  decide +kernel

theorem trig2_g1 : trig2Tab.Group trig2C (1, 13, 14) :=
  ⟨_, _, trig2_s1, trig2_c1, trig2_ok1⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok1 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 1 13 14 (dySt trig2_s1_11) (dySt trig2_c1_12) := by
  decide +kernel

theorem tan2_g1 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (1, 13, 14) :=
  ⟨_, _, trig2_s1, trig2_c1, tan2_ok1⟩

def trig2_s2_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((636723062471040373879669005184109568150409123212687808605297, 353),
    [(1271658239383111532436168466909574357242841981523744058054945, 248),
     (317914559845777972381059604564230531546598008051444090758619, 299)])

def trig2_s2_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((703429022846099692596554219910288124084127592403941883602211, 337),
    [(1108354471337331096386015973356251309482110072457210742954273, 232),
     (277088617834332857355975726636072610230973909893697848302543, 283)])

def trig2_s2_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1453085436236022997472756196243926205851521453325813909782045, 324),
    [(580424887943988086364258853234657147030870722755348805490749, 217),
     (1160849775887976508920064165028631749094064529687293255276107, 271)])

def trig2_s2_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((218563623673169487987698796982657643113545471722968162355943, 310),
    [(857033623604794908772225962979290919825321360590769446924587, 206),
     (857033623604795111248833162336730860359149681184530605725837, 259)])

def trig2_s2_9 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((337306417171699589592515708850489005000955998584077052884477, 306),
    [(535646014752996817982641226862060902619263720199408758446331, 201),
     (66955751844124620878244371296885983293320848371189712556337, 251)])

set_option maxHeartbeats 4000000 in
theorem trig2_s2_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 2 10 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 10) = dySt trig2_s2_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s2_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 2 10 2 2 (dySt trig2_s2_2) = dySt trig2_s2_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s2_4_6 :
    trig2Tab.run sinCQ trig2Tab.FsQ 2 10 4 2 (dySt trig2_s2_4) = dySt trig2_s2_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s2_6_8 :
    trig2Tab.run sinCQ trig2Tab.FsQ 2 10 6 2 (dySt trig2_s2_6) = dySt trig2_s2_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s2_8_9 :
    trig2Tab.run sinCQ trig2Tab.FsQ 2 10 8 1 (dySt trig2_s2_8) = dySt trig2_s2_9 := by
  decide +kernel

theorem trig2_s2 : trig2Tab.run sinCQ trig2Tab.FsQ 2 10 0 9 (trig2Tab.init sinCQ trig2Tab.FsQ 10) =
    dySt trig2_s2_9 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 2 10 _ 2 7 trig2_s2_0_2
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 2 10 _ 2 5 trig2_s2_2_4
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 2 10 _ 2 3 trig2_s2_4_6
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 2 10 _ 2 1 trig2_s2_6_8
    (trig2_s2_8_9))))

def trig2_c2_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((699842159558867247688991179759837060584510269854678495305887, 357),
    [(1130362879451654695498816415030738262320939766337522437280709, 252),
     (1130362879451655032728731947031383053332806131349459751364805, 305)])

def trig2_c2_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1329400034659624586705076010755881511509962262146028502854603, 342),
    [(316672706096380313253147420958925965090464473652335293130679, 234),
     (9896022065511887165290282601142342584495120839770962829441, 282)])

def trig2_c2_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((509623084915475435009935111174341080125297589787999636468827, 326),
    [(464339910355190469091407082587725803607416649134680010676465, 220),
     (58042488794398826536614650632203674253452169761371709162035, 270)])

def trig2_c2_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1262596998818188416711145876706689117231189977699061906701185, 315),
    [(571355749069863272514817308652862745866886741829285335804501, 208),
     (571355749069863421328043998530260190827802022649907812362989, 261)])

def trig2_c2_10 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((817096478467180765008420737781802180439068609947983607323965, 306),
    [(803469022129495226973961840293084042057326661076081021471389, 200),
     (100433627766186925788640143142942973169759496994221778566433, 250)])

set_option maxHeartbeats 4000000 in
theorem trig2_c2_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 2 11 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 11) = dySt trig2_c2_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c2_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 2 11 2 2 (dySt trig2_c2_2) = dySt trig2_c2_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c2_4_6 :
    trig2Tab.run cosCQ trig2Tab.FcQ 2 11 4 2 (dySt trig2_c2_4) = dySt trig2_c2_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c2_6_8 :
    trig2Tab.run cosCQ trig2Tab.FcQ 2 11 6 2 (dySt trig2_c2_6) = dySt trig2_c2_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c2_8_10 :
    trig2Tab.run cosCQ trig2Tab.FcQ 2 11 8 2 (dySt trig2_c2_8) = dySt trig2_c2_10 := by
  decide +kernel

theorem trig2_c2 : trig2Tab.run cosCQ trig2Tab.FcQ 2 11 0 10 (trig2Tab.init cosCQ trig2Tab.FcQ 11) =
    dySt trig2_c2_10 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 2 11 _ 2 8 trig2_c2_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 2 11 _ 2 6 trig2_c2_2_4
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 2 11 _ 2 4 trig2_c2_4_6
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 2 11 _ 2 2 trig2_c2_6_8
    (trig2_c2_8_10))))

set_option maxHeartbeats 4000000 in
theorem trig2_ok2 : trig2Tab.Ok trig2C 2 11 12 (dySt trig2_s2_9) (dySt trig2_c2_10) := by
  decide +kernel

theorem trig2_g2 : trig2Tab.Group trig2C (2, 11, 12) :=
  ⟨_, _, trig2_s2, trig2_c2, trig2_ok2⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok2 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 2 11 12 (dySt trig2_s2_9) (dySt trig2_c2_10) := by
  decide +kernel

theorem tan2_g2 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (2, 11, 12) :=
  ⟨_, _, trig2_s2, trig2_c2, tan2_ok2⟩

def trig2_s3_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1352491827153636870208293491629061255733273562644600096154685, 346),
    [(337784219836139000803357249022853829010737514446319978508335, 238),
     (1351136879344556315679675032620206883620646316860957495276167, 293)])

def trig2_s3_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1440606033754308759227381251753384582365738678693396553049345, 331),
    [(168850876492796534215057120940990602451211020104830759299463, 222),
     (1350807011942372651809808438475964265670398889004384523448179, 278)])

def trig2_s3_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((326739228741760090452180838538731382051846578859878664961465, 316),
    [(652977998936986597159791209888982438752912687144900172208193, 211),
     (1305955997873973485495732073679088198811185131530831064243773, 265)])

def trig2_s3_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((670819944601543337746940143288564211481140094168425232124491, 307),
    [(1071292029505993635965282453724121649839574377258128890794557, 202),
     (535646014752996966747195655393454318510872170031233584804779, 254)])

set_option maxHeartbeats 4000000 in
theorem trig2_s3_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 3 9 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 9) = dySt trig2_s3_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s3_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 3 9 2 2 (dySt trig2_s3_2) = dySt trig2_s3_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s3_4_6 :
    trig2Tab.run sinCQ trig2Tab.FsQ 3 9 4 2 (dySt trig2_s3_4) = dySt trig2_s3_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s3_6_8 :
    trig2Tab.run sinCQ trig2Tab.FsQ 3 9 6 2 (dySt trig2_s3_6) = dySt trig2_s3_8 := by
  decide +kernel

theorem trig2_s3 : trig2Tab.run sinCQ trig2Tab.FsQ 3 9 0 8 (trig2Tab.init sinCQ trig2Tab.FsQ 9) =
    dySt trig2_s3_8 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 3 9 _ 2 6 trig2_s3_0_2
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 3 9 _ 2 4 trig2_s3_2_4
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 3 9 _ 2 2 trig2_s3_4_6
    (trig2_s3_6_8)))

def trig2_c3_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((20760272168763317999195585922295383281830032044616925922795, 336),
    [(633345412192760626506294841917851922554758128422751208752899, 235),
     (1266690824385521557102222215199570238701284406412658819227005, 289)])

def trig2_c3_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1018234561900744266625864741559175878452044965722609079522245, 327),
    [(928679820710380938182814165175451586615928888438911184812651, 221),
     (928679820710381224512607015267429959139642842656319085741291, 274)])

def trig2_c3_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((629862418134602611498329272040995429737072124748269163374363, 314),
    [(285677874534931636257408654326431358187956629714122091601445, 207),
     (571355749069863421221849973775352172713507364870603992060819, 261)])

def trig2_c3_8 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((806870809361047853714461004901785216534117792747358813000345, 306),
    [(200867255532373806743490460073270959661242818799973245149711, 198),
     (803469022129495405612222857689459906605175376657732012049453, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_c3_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 3 9 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 9) = dySt trig2_c3_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c3_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 3 9 2 2 (dySt trig2_c3_2) = dySt trig2_c3_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c3_4_6 :
    trig2Tab.run cosCQ trig2Tab.FcQ 3 9 4 2 (dySt trig2_c3_4) = dySt trig2_c3_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c3_6_8 :
    trig2Tab.run cosCQ trig2Tab.FcQ 3 9 6 2 (dySt trig2_c3_6) = dySt trig2_c3_8 := by
  decide +kernel

theorem trig2_c3 : trig2Tab.run cosCQ trig2Tab.FcQ 3 9 0 8 (trig2Tab.init cosCQ trig2Tab.FcQ 9) =
    dySt trig2_c3_8 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 3 9 _ 2 6 trig2_c3_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 3 9 _ 2 4 trig2_c3_2_4
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 3 9 _ 2 2 trig2_c3_4_6
    (trig2_c3_6_8)))

set_option maxHeartbeats 4000000 in
theorem trig2_ok3 : trig2Tab.Ok trig2C 3 10 10 (dySt trig2_s3_8) (dySt trig2_c3_8) := by
  decide +kernel

theorem trig2_g3 : trig2Tab.Group trig2C (3, 10, 10) :=
  ⟨_, _, trig2_s3, trig2_c3, trig2_ok3⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok3 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 3 10 10 (dySt trig2_s3_8) (dySt trig2_c3_8) := by
  decide +kernel

theorem tan2_g3 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (3, 10, 10) :=
  ⟨_, _, trig2_s3, trig2_c3, tan2_ok3⟩

def trig2_s4_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1405929809907321982460857871935431173394753448976563416395201, 338),
    [(1108354471337331096386015973356251290417102583240785942684559, 232),
     (277088617834332857338808864840244606445425342803908627045999, 283)])

def trig2_s4_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((725594310130981763399756417384992427667973194860609818197087, 323),
    [(580424887943988086364258853234657127719082880140079412130927, 217),
     (1160849775887976508782762799688952694876699850028293047769607, 271)])

def trig2_s4_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((870663920578946652100378068156253910936558538253489300544155, 312),
    [(857033623604794908772225962979290846093315620131263019094373, 206),
     (428516811802397555491674050224730407534420501139683753471949, 258)])

def trig2_s4_7 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1339746074765253428253595064902458417364887327684704812660145, 308),
    [(1071292029505993635965282453724121611022258702600885298833853, 202),
     (535646014752996966677505826648045931568159811360626844773029, 254)])

set_option maxHeartbeats 4000000 in
theorem trig2_s4_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 4 8 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 8) = dySt trig2_s4_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s4_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 4 8 2 2 (dySt trig2_s4_2) = dySt trig2_s4_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s4_4_6 :
    trig2Tab.run sinCQ trig2Tab.FsQ 4 8 4 2 (dySt trig2_s4_4) = dySt trig2_s4_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s4_6_7 :
    trig2Tab.run sinCQ trig2Tab.FsQ 4 8 6 1 (dySt trig2_s4_6) = dySt trig2_s4_7 := by
  decide +kernel

theorem trig2_s4 : trig2Tab.run sinCQ trig2Tab.FsQ 4 8 0 7 (trig2Tab.init sinCQ trig2Tab.FsQ 8) =
    dySt trig2_s4_7 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 4 8 _ 2 5 trig2_s4_0_2
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 4 8 _ 2 3 trig2_s4_2_4
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 4 8 _ 2 1 trig2_s4_4_6
    (trig2_s4_6_7)))

def trig2_c4_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((240042030798436516036319095332111166156487475980353592779569, 332),
    [(112567250995197689476704747293993734385628685539857069219447, 225),
     (900538007961581767857469335671133840024481332875805913775279, 281)])

def trig2_c4_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1306211204012899601788769410509018903895064650385081390584949, 321),
    [(652977998936986597159791209888982431362469926148309425984907, 214),
     (652977998936986742722694119860602939156288489123606748914227, 267)])

def trig2_c4_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((669773853296849957217499073852360601679608660642243459138021, 309),
    [(1071292029505993635965282453724121606857821046633900148314591, 204),
     (1071292029505993933339525024686001110630980962011605309438133, 257)])

def trig2_c4_7 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((804319151955082826479961086639447684070576620404361416005893, 306),
    [(401734511064747613486980920146541893925276181593278991884693, 199),
     (803469022129495405437998285825938936975620161289433495052945, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_c4_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 4 8 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 8) = dySt trig2_c4_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c4_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 4 8 2 2 (dySt trig2_c4_2) = dySt trig2_c4_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c4_4_6 :
    trig2Tab.run cosCQ trig2Tab.FcQ 4 8 4 2 (dySt trig2_c4_4) = dySt trig2_c4_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c4_6_7 :
    trig2Tab.run cosCQ trig2Tab.FcQ 4 8 6 1 (dySt trig2_c4_6) = dySt trig2_c4_7 := by
  decide +kernel

theorem trig2_c4 : trig2Tab.run cosCQ trig2Tab.FcQ 4 8 0 7 (trig2Tab.init cosCQ trig2Tab.FcQ 8) =
    dySt trig2_c4_7 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 4 8 _ 2 5 trig2_c4_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 4 8 _ 2 3 trig2_c4_2_4
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 4 8 _ 2 1 trig2_c4_4_6
    (trig2_c4_6_7)))

set_option maxHeartbeats 4000000 in
theorem trig2_ok4 : trig2Tab.Ok trig2C 4 9 9 (dySt trig2_s4_7) (dySt trig2_c4_7) := by
  decide +kernel

theorem trig2_g4 : trig2Tab.Group trig2C (4, 9, 9) :=
  ⟨_, _, trig2_s4, trig2_c4, trig2_ok4⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok4 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 4 9 9 (dySt trig2_s4_7) (dySt trig2_c4_7) := by
  decide +kernel

theorem tan2_g4 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (4, 9, 9) :=
  ⟨_, _, trig2_s4, trig2_c4, tan2_ok4⟩

def trig2_s5_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((360047858149632288485623747102376389323414158815335590426859, 329),
    [(675403505971186136860228483763962405686229877841336107010669, 224),
     (1350807011942372651781644055842183946542136843965649209270781, 278)])

def trig2_s5_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((653046637680292783605265291636298067732282811048102220227735, 317),
    [(326488999468493298579895604944491215077674512352730034478049, 210),
     (1305955997873973485436735393259694854603101598108471110210807, 265)])

def trig2_s5_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1339272785405759103579133696596209573236249830868128698355241, 308),
    [(1071292029505993635965282453724121601319954321050221438360513, 202),
     (1071292029505993933320166738923387669666987980499597357871123, 255)])

set_option maxHeartbeats 4000000 in
theorem trig2_s5_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 5 7 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 7) = dySt trig2_s5_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s5_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 5 7 2 2 (dySt trig2_s5_2) = dySt trig2_s5_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s5_4_6 :
    trig2Tab.run sinCQ trig2Tab.FsQ 5 7 4 2 (dySt trig2_s5_4) = dySt trig2_s5_6 := by
  decide +kernel

theorem trig2_s5 : trig2Tab.run sinCQ trig2Tab.FsQ 5 7 0 6 (trig2Tab.init sinCQ trig2Tab.FsQ 7) =
    dySt trig2_s5_6 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 5 7 _ 2 4 trig2_s5_0_2
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 5 7 _ 2 2 trig2_s5_2_4
    (trig2_s5_4_6))

def trig2_c5_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((254479635157867404685736778151054095583507647130914487068951, 325),
    [(928679820710380938182814165175451580180080386316316594481539, 221),
     (464339910355190612244861727188741725052414754064490462922185, 273)])

def trig2_c5_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1258827918476551590305884238127338505096883931280154736069069, 315),
    [(1142711498139726545029634617305725414327770467862313196372777, 209),
     (285677874534931710594332170519721708528345736033904662483435, 260)])

def trig2_c5_6 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((803681534779510673400997631355693665258640752412422248332459, 306),
    [(803469022129495226973961840293083775155610611191881334282309, 200),
     (401734511064747702697221071430029347285947166728007983503133, 252)])

set_option maxHeartbeats 4000000 in
theorem trig2_c5_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 5 7 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 7) = dySt trig2_c5_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c5_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 5 7 2 2 (dySt trig2_c5_2) = dySt trig2_c5_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c5_4_6 :
    trig2Tab.run cosCQ trig2Tab.FcQ 5 7 4 2 (dySt trig2_c5_4) = dySt trig2_c5_6 := by
  decide +kernel

theorem trig2_c5 : trig2Tab.run cosCQ trig2Tab.FcQ 5 7 0 6 (trig2Tab.init cosCQ trig2Tab.FcQ 7) =
    dySt trig2_c5_6 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 5 7 _ 2 4 trig2_c5_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 5 7 _ 2 2 trig2_c5_2_4
    (trig2_c5_4_6))

set_option maxHeartbeats 4000000 in
theorem trig2_ok5 : trig2Tab.Ok trig2C 5 8 8 (dySt trig2_s5_6) (dySt trig2_c5_6) := by
  decide +kernel

theorem trig2_g5 : trig2Tab.Group trig2C (5, 8, 8) :=
  ⟨_, _, trig2_s5, trig2_c5, trig2_ok5⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok5 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 5 8 8 (dySt trig2_s5_6) (dySt trig2_c5_6) := by
  decide +kernel

theorem tan2_g5 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (5, 8, 8) :=
  ⟨_, _, trig2_s5, trig2_c5, tan2_ok5⟩

def trig2_s6_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1451070119683376710020076954264422426914295144482070678114593, 324),
    [(36276555496499255397766178327166070407025429745941116811177, 213),
     (580424887943988254387090732177611376994368014733235561457721, 270)])

def trig2_s6_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((108804964976613762277941259959731891221060745733891296537801, 309),
    [(857033623604794908772225962979290841487655141891374597133613, 206),
     (428516811802397555483377642040753218620393295193312772044051, 258)])

def trig2_s6_5 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1339154473329132908700804687576204497271131586536946109075795, 308),
    [(1071292029505993635965282453724121598894504729953550100423467, 202),
     (1071292029505993933311455510330211621299781574235177902185175, 255)])

set_option maxHeartbeats 4000000 in
theorem trig2_s6_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 6 6 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 6) = dySt trig2_s6_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s6_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 6 6 2 2 (dySt trig2_s6_2) = dySt trig2_s6_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s6_4_5 :
    trig2Tab.run sinCQ trig2Tab.FsQ 6 6 4 1 (dySt trig2_s6_4) = dySt trig2_s6_5 := by
  decide +kernel

theorem trig2_s6 : trig2Tab.run sinCQ trig2Tab.FsQ 6 6 0 5 (trig2Tab.init sinCQ trig2Tab.FsQ 6) =
    dySt trig2_s6_5 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 6 6 _ 2 3 trig2_s6_0_2
    (TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 6 6 _ 2 1 trig2_s6_2_4
    (trig2_s6_4_5))

def trig2_c6_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1306046675351355117051980385578685063437782551922511245840263, 321),
    [(1305955997873973194319582419777964859386978066473121378786535, 215),
     (652977998936986742716794451818663604786011975357510048248359, 267)])

def trig2_c6_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1339142077028952322559032327474383723073211319250243901192213, 310),
    [(535646014752996817982641226862060799317124230253766070900879, 203),
     (1071292029505993933310487596042080949268218991992743491722757, 257)])

def trig2_c6_5 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((401761074527089368414634395923404701443253513161517501627935, 305),
    [(803469022129495226973961840293083771982104048379451815092437, 200),
     (200867255532373851345888276779647158492797937920975307067277, 251)])

set_option maxHeartbeats 4000000 in
theorem trig2_c6_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 6 6 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 6) = dySt trig2_c6_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c6_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 6 6 2 2 (dySt trig2_c6_2) = dySt trig2_c6_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c6_4_5 :
    trig2Tab.run cosCQ trig2Tab.FcQ 6 6 4 1 (dySt trig2_c6_4) = dySt trig2_c6_5 := by
  decide +kernel

theorem trig2_c6 : trig2Tab.run cosCQ trig2Tab.FcQ 6 6 0 5 (trig2Tab.init cosCQ trig2Tab.FcQ 6) =
    dySt trig2_c6_5 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 6 6 _ 2 3 trig2_c6_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 6 6 _ 2 1 trig2_c6_2_4
    (trig2_c6_4_5))

set_option maxHeartbeats 4000000 in
theorem trig2_ok6 : trig2Tab.Ok trig2C 6 7 7 (dySt trig2_s6_5) (dySt trig2_c6_5) := by
  decide +kernel

theorem trig2_g6 : trig2Tab.Group trig2C (6, 7, 7) :=
  ⟨_, _, trig2_s6, trig2_c6, trig2_ok6⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok6 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 6 7 7 (dySt trig2_s6_5) (dySt trig2_c6_5) := by
  decide +kernel

theorem tan2_g6 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (6, 7, 7) :=
  ⟨_, _, trig2_s6, trig2_c6, tan2_ok6⟩

def trig2_s7_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((326509826272408052607188716886592246334602719776228409491993, 316),
    [(1305955997873973194319582419777964859236091393309148998124983, 212),
     (652977998936986742716524050366741385295092589486366243119527, 264)])

def trig2_s7_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((334781223987848052883286472384039911970880345439868538186463, 306),
    [(133911503688249204495660306715515199786018779780019030032483, 199),
     (267823007376498483327319425795479402301996969682460753146891, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_s7_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 7 5 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 5) = dySt trig2_s7_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s7_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 7 5 2 2 (dySt trig2_s7_2) = dySt trig2_s7_4 := by
  decide +kernel

theorem trig2_s7 : trig2Tab.run sinCQ trig2Tab.FsQ 7 5 0 4 (trig2Tab.init sinCQ trig2Tab.FsQ 5) =
    dySt trig2_s7_4 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 7 5 _ 2 2 trig2_s7_0_2
    (trig2_s7_2_4)

def trig2_c7_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1306038449162070027577819890062825382179548611533594457961373, 321),
    [(1305955997873973194319582419777964859220082982152010796531159, 215),
     (326488999468493371358249734208283319033749826077118679458783, 266)])

def trig2_c7_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((669560898448863651293873357578805365344645982813243565305675, 309),
    [(1071292029505993635965282453724121598223086434410422424391141, 204),
     (1071292029505993933309035724609884941200097496701009083758771, 257)])

def trig2_c7_5 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((100435287972912968001736920185552443457385050817690340733181, 303),
    [(200867255532373806743490460073270942797185427856357630758069, 198),
     (401734511064747702690415424091610559410515204994979315663957, 252)])

set_option maxHeartbeats 4000000 in
theorem trig2_c7_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 7 6 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 6) = dySt trig2_c7_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c7_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 7 6 2 2 (dySt trig2_c7_2) = dySt trig2_c7_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c7_4_5 :
    trig2Tab.run cosCQ trig2Tab.FcQ 7 6 4 1 (dySt trig2_c7_4) = dySt trig2_c7_5 := by
  decide +kernel

theorem trig2_c7 : trig2Tab.run cosCQ trig2Tab.FcQ 7 6 0 5 (trig2Tab.init cosCQ trig2Tab.FcQ 6) =
    dySt trig2_c7_5 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 7 6 _ 2 3 trig2_c7_0_2
    (TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 7 6 _ 2 1 trig2_c7_2_4
    (trig2_c7_4_5))

set_option maxHeartbeats 4000000 in
theorem trig2_ok7 : trig2Tab.Ok trig2C 7 6 7 (dySt trig2_s7_4) (dySt trig2_c7_5) := by
  decide +kernel

theorem trig2_g7 : trig2Tab.Group trig2C (7, 6, 7) :=
  ⟨_, _, trig2_s7, trig2_c7, trig2_ok7⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok7 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 7 6 7 (dySt trig2_s7_4) (dySt trig2_c7_5) := by
  decide +kernel

theorem tan2_g7 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (7, 6, 7) :=
  ⟨_, _, trig2_s7, trig2_c7, tan2_ok7⟩

def trig2_s8_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((81627287912433731349960471358679531174487312128078624326111, 314),
    [(1305955997873973194319582419777964859182361342215645212436551, 212),
     (1305955997873973485432863736107172166389539639727530326341509, 265)])

def trig2_s8_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1339117501647044948137404278993831677775970396141221753273455, 308),
    [(33477875922062301123915076678878799941767565919795437299015, 197),
     (133911503688249241663591656424355513273129993621895063567235, 252)])

set_option maxHeartbeats 4000000 in
theorem trig2_s8_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 8 5 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 5) = dySt trig2_s8_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s8_2_4 :
    trig2Tab.run sinCQ trig2Tab.FsQ 8 5 2 2 (dySt trig2_s8_2) = dySt trig2_s8_4 := by
  decide +kernel

theorem trig2_s8 : trig2Tab.run sinCQ trig2Tab.FsQ 8 5 0 4 (trig2Tab.init sinCQ trig2Tab.FsQ 5) =
    dySt trig2_s8_4 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 8 5 _ 2 2 trig2_s8_0_2
    (trig2_s8_2_4)

def trig2_c8_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((629384534390588989360470482307212934863622603639093137605541, 314),
    [(285677874534931636257408654326431353279705410143146243681607, 207),
     (1142711498139726842372973067782298809933555709262016373817287, 262)])

def trig2_c8_4 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((803472342538112415985373069106505082242574505366638827463571, 306),
    [(401734511064747613486980920146541885495201010578199575387185, 199),
     (803469022129495405380150283449379240033490968535946932850111, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_c8_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 8 5 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 5) = dySt trig2_c8_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c8_2_4 :
    trig2Tab.run cosCQ trig2Tab.FcQ 8 5 2 2 (dySt trig2_c8_2) = dySt trig2_c8_4 := by
  decide +kernel

theorem trig2_c8 : trig2Tab.run cosCQ trig2Tab.FcQ 8 5 0 4 (trig2Tab.init cosCQ trig2Tab.FcQ 5) =
    dySt trig2_c8_4 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 8 5 _ 2 2 trig2_c8_0_2
    (trig2_c8_2_4)

set_option maxHeartbeats 4000000 in
theorem trig2_ok8 : trig2Tab.Ok trig2C 8 6 6 (dySt trig2_s8_4) (dySt trig2_c8_4) := by
  decide +kernel

theorem trig2_g8 : trig2Tab.Group trig2C (8, 6, 6) :=
  ⟨_, _, trig2_s8, trig2_c8, trig2_ok8⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok8 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 8 6 6 (dySt trig2_s8_4) (dySt trig2_c8_4) := by
  decide +kernel

theorem tan2_g8 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (8, 6, 6) :=
  ⟨_, _, trig2_s8, trig2_c8, tan2_ok8⟩

def trig2_s10_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((870424832355590998064752190883738132914394411434309260668047, 312),
    [(857033623604794908772225962979290841181821283507099994263333, 206),
     (857033623604795110965653417369571966838153134845716135772089, 259)])

def trig2_s10_3 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1339115190930224877734502784533368397209295197644839581003167, 308),
    [(1071292029505993635965282453724121598089190859714629181783753, 202),
     (267823007376498483327140777552845909122592190365022654082175, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_s10_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 10 4 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 4) = dySt trig2_s10_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_s10_2_3 :
    trig2Tab.run sinCQ trig2Tab.FsQ 10 4 2 1 (dySt trig2_s10_2) = dySt trig2_s10_3 := by
  decide +kernel

theorem trig2_s10 : trig2Tab.run sinCQ trig2Tab.FsQ 10 4 0 3 (trig2Tab.init sinCQ trig2Tab.FsQ 4) =
    dySt trig2_s10_3 :=
  TrigTab.run_cut trig2Tab sinCQ trig2Tab.FsQ 10 4 _ 2 1 trig2_s10_0_2
    (trig2_s10_2_3)

def trig2_c10_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((669557571253810199275345685563738769755325065990181435702951, 309),
    [(1071292029505993635965282453724121598088174239123750018465481, 204),
     (1071292029505993933308559329296195626052745475584850451245427, 257)])

def trig2_c10_3 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((803469229654939615921744569725358807896278645168281506994503, 306),
    [(803469022129495226973961840293083770928420941280452219453311, 200),
     (803469022129495405379937606970053652912384966414693649585365, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_c10_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 10 4 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 4) = dySt trig2_c10_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_c10_2_3 :
    trig2Tab.run cosCQ trig2Tab.FcQ 10 4 2 1 (dySt trig2_c10_2) = dySt trig2_c10_3 := by
  decide +kernel

theorem trig2_c10 : trig2Tab.run cosCQ trig2Tab.FcQ 10 4 0 3 (trig2Tab.init cosCQ trig2Tab.FcQ 4) =
    dySt trig2_c10_3 :=
  TrigTab.run_cut trig2Tab cosCQ trig2Tab.FcQ 10 4 _ 2 1 trig2_c10_0_2
    (trig2_c10_2_3)

set_option maxHeartbeats 4000000 in
theorem trig2_ok10 : trig2Tab.Ok trig2C 10 5 5 (dySt trig2_s10_3) (dySt trig2_c10_3) := by
  decide +kernel

theorem trig2_g10 : trig2Tab.Group trig2C (10, 5, 5) :=
  ⟨_, _, trig2_s10, trig2_c10, trig2_ok10⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok10 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 10 5 5 (dySt trig2_s10_3) (dySt trig2_c10_3) := by
  decide +kernel

theorem tan2_g10 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (10, 5, 5) :=
  ⟨_, _, trig2_s10, trig2_c10, tan2_ok10⟩

def trig2_s13_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((669557519644744157124036503130923810721674013682816283323525, 307),
    [(267823007376498408991320613431030399521520530531680486395377, 200),
     (66955751844124620831784496543513690197915997840894049795225, 251)])

set_option maxHeartbeats 4000000 in
theorem trig2_s13_0_2 :
    trig2Tab.run sinCQ trig2Tab.FsQ 13 3 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 3) = dySt trig2_s13_2 := by
  decide +kernel

theorem trig2_s13 : trig2Tab.run sinCQ trig2Tab.FsQ 13 3 0 2 (trig2Tab.init sinCQ trig2Tab.FsQ 3) =
    dySt trig2_s13_2 :=
  trig2_s13_0_2

def trig2_c13_2 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((200867256343020115412308341380144237253687238669155559759639, 304),
    [(100433627766186903371745230036635471365544179266826373800997, 197),
     (401734511064747702689961825038048955628781193123252095596863, 252)])

set_option maxHeartbeats 4000000 in
theorem trig2_c13_0_2 :
    trig2Tab.run cosCQ trig2Tab.FcQ 13 3 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 3) = dySt trig2_c13_2 := by
  decide +kernel

theorem trig2_c13 : trig2Tab.run cosCQ trig2Tab.FcQ 13 3 0 2 (trig2Tab.init cosCQ trig2Tab.FcQ 3) =
    dySt trig2_c13_2 :=
  trig2_c13_0_2

set_option maxHeartbeats 4000000 in
theorem trig2_ok13 : trig2Tab.Ok trig2C 13 4 4 (dySt trig2_s13_2) (dySt trig2_c13_2) := by
  decide +kernel

theorem trig2_g13 : trig2Tab.Group trig2C (13, 4, 4) :=
  ⟨_, _, trig2_s13, trig2_c13, trig2_ok13⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok13 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 13 4 4 (dySt trig2_s13_2) (dySt trig2_c13_2) := by
  decide +kernel

theorem tan2_g13 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (13, 4, 4) :=
  ⟨_, _, trig2_s13, trig2_c13, tan2_ok13⟩

def trig2_s18_1 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((1339115036884063664700291635680735849738080421225188102602173, 308),
    [(1071292029505993635965282453724121598086032815667154598826481, 202),
     (535646014752996966654275883819448083564276028420857645201577, 254)])

set_option maxHeartbeats 4000000 in
theorem trig2_s18_0_1 :
    trig2Tab.run sinCQ trig2Tab.FsQ 18 2 0 1 (trig2Tab.init sinCQ trig2Tab.FsQ 2) = dySt trig2_s18_1 := by
  decide +kernel

theorem trig2_s18 : trig2Tab.run sinCQ trig2Tab.FsQ 18 2 0 1 (trig2Tab.init sinCQ trig2Tab.FsQ 2) =
    dySt trig2_s18_1 :=
  trig2_s18_0_1

def trig2_c18_1 : (ℤ × ℕ) × List (ℤ × ℕ) :=
  ((401734511065843873519450298227481557570047557350326627147277, 305),
    [(803469022129495226973961840293083770924288921571135946315389, 200),
     (803469022129495405379923428754444316209929625495351075013403, 253)])

set_option maxHeartbeats 4000000 in
theorem trig2_c18_0_1 :
    trig2Tab.run cosCQ trig2Tab.FcQ 18 2 0 1 (trig2Tab.init cosCQ trig2Tab.FcQ 2) = dySt trig2_c18_1 := by
  decide +kernel

theorem trig2_c18 : trig2Tab.run cosCQ trig2Tab.FcQ 18 2 0 1 (trig2Tab.init cosCQ trig2Tab.FcQ 2) =
    dySt trig2_c18_1 :=
  trig2_c18_0_1

set_option maxHeartbeats 4000000 in
theorem trig2_ok18 : trig2Tab.Ok trig2C 18 3 3 (dySt trig2_s18_1) (dySt trig2_c18_1) := by
  decide +kernel

theorem trig2_g18 : trig2Tab.Group trig2C (18, 3, 3) :=
  ⟨_, _, trig2_s18, trig2_c18, trig2_ok18⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok18 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 18 3 3 (dySt trig2_s18_1) (dySt trig2_c18_1) := by
  decide +kernel

theorem tan2_g18 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (18, 3, 3) :=
  ⟨_, _, trig2_s18, trig2_c18, tan2_ok18⟩

theorem trig2_s28 : trig2Tab.run sinCQ trig2Tab.FsQ 28 1 0 0 (trig2Tab.init sinCQ trig2Tab.FsQ 1) =
    trig2Tab.init sinCQ trig2Tab.FsQ 1 := rfl

theorem trig2_c28 : trig2Tab.run cosCQ trig2Tab.FcQ 28 1 0 0 (trig2Tab.init cosCQ trig2Tab.FcQ 1) =
    trig2Tab.init cosCQ trig2Tab.FcQ 1 := rfl

set_option maxHeartbeats 4000000 in
theorem trig2_ok28 : trig2Tab.Ok trig2C 28 2 2 (trig2Tab.init sinCQ trig2Tab.FsQ 1) (trig2Tab.init cosCQ trig2Tab.FcQ 1) := by
  decide +kernel

theorem trig2_g28 : trig2Tab.Group trig2C (28, 2, 2) :=
  ⟨_, _, trig2_s28, trig2_c28, trig2_ok28⟩

set_option maxHeartbeats 4000000 in
theorem tan2_ok28 :
    trig2Tab.TanOk trig2Ct trig2Kd0 trig2Kd3 28 2 2 (trig2Tab.init sinCQ trig2Tab.FsQ 1) (trig2Tab.init cosCQ trig2Tab.FcQ 1) := by
  decide +kernel

theorem tan2_g28 : trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 (28, 2, 2) :=
  ⟨_, _, trig2_s28, trig2_c28, tan2_ok28⟩

end ExpansionBounds
