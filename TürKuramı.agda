module TürKuramı where

-- Jesper Cocks'un "Programming and Proving in Agda" öğretgesindeki
-- izgeler Türkçeleştirilmiştir. İzgeler Türkçeleştirilirken, işlev ve
-- türlerde Türkçe'nin doğasına uygun bazı yapı değişiklikleri yapılmıştır.
-- Türkçede konunun daha rahat anlaşılmasına yardımcı olacak sezgisel olarak
-- güçlü ifadeler seçilmeye çalışılmıştır.

-- Bu öğretge bağımlı türler konusuna kuramsal ve uygulamasal açıdan giriş
-- için kullanılabilecek en uygun metinlerden biridir.

-- Bu izge dosyasında standart kütüphane kullanılmamış, gerekli olan her tür
-- ve işlev kendi içinde tanımlanmıştır. Bu anlamda kendi kendine yeten
-- bir agda dosyasıdır.


  -- Tür kuramında türe küme demeyelim
Tür = Set

data Selamlama : Tür where
  merhaba : Selamlama

selam : Selamlama
selam = merhaba


data Doğruluk : Tür where
  doğru  : Doğruluk
  yanlış : Doğruluk

_değil : Doğruluk → Doğruluk
doğru değil = yanlış
yanlış değil = doğru

_ve_ : Doğruluk → Doğruluk → Doğruluk
doğru ve b = b
yanlış ve _ = yanlış

_veya_ : Doğruluk → Doğruluk → Doğruluk
doğru veya _ = doğru
yanlış veya b = b

_ise_ : Doğruluk → Doğruluk → Doğruluk
doğru ise b = b
yanlış ise _ = doğru


data Doğal : Tür where
  sıfır : Doğal
  ard   : Doğal → Doğal

-- Bu eklenti sayesinde tanımladığımız Doğal
-- ilişkilendiriliyor ki normal rakamlar ile
-- türümüz Agda'nın kendi eşlenik türü ile
-- doğal sayıları ifade edebilelim.
{-# BUILTIN NATURAL Doğal #-}

-- Doğal sayılarda toplama işlemi
_+_ : Doğal → Doğal → Doğal
sıfır + b = b
ard a + b = ard (a + b)

-- aşağıya yuvarlayan tamsayı ikiye bölme
_yarısı : Doğal → Doğal
sıfır yarısı         = sıfır
(ard sıfır) yarısı   = sıfır
(ard (ard a)) yarısı = 1 + (a yarısı)

-- Doğal sayılarda çarpma işlemi
_×_ : Doğal → Doğal → Doğal
sıfır × _ = sıfır
ard a × b = b + (a × b)
-- (1 + a) × b  = b + ab

-- Türleri değişkenlere atamak
BenimDoğal : Tür
BenimDoğal = Doğal

-- Her tür için çalışan '_aynı' işlevi
-- A bir tür değişkenidir.
_aynı : {A : Tür} → A → A
a aynı = a

-- koşullu ifade
eğer_ise_değilse_ : {A : Tür} → Doğruluk → A → A → A
eğer doğru ise a değilse b  = a
eğer yanlış ise a değilse b = b


-- Çok türlü veri yapısı : Dizelge
data Dizelge (A : Tür) : Tür where
  []   : Dizelge A
  _::_ : A → Dizelge A → Dizelge A

-- işleme öncelik sırası tanımlıyoruz.
infixr 5 _::_

-- Çift/Çarpım türü
data _x_ (A B : Tür) : Tür where
  _,_ : A → B → A x B

infixr 4 _,_

çift1 : Doğal x Doğruluk
çift1 = (3 , yanlış)

birinci : {A B : Tür} → A x B → A
birinci (a , b) = a

ikinci : {A B : Tür} → A x B → B
ikinci (a , b) = b

-- uzunluk işlevi
_uzunluk : {A : Tür} → Dizelge A → Doğal
[] uzunluk = 0
(a :: alar) uzunluk = 1 + (alar uzunluk)

-- Dizelgeleri birleştirme işlevi
_++_ : {A : Tür} → Dizelge A → Dizelge A → Dizelge A
[] ++ b = b
(x :: a) ++ b = x :: (a ++ b)

-- Dizelgeyi bir işlev ile dönüştürme
eşle : {A B : Tür} → Dizelge A → (A → B) → Dizelge B
eşle [] f = []
eşle (x :: l) f = (f x) :: eşle l f


data Belki (A : Tür) : Tür where
  sadece    : A → Belki A
  hiçbirşey : Belki A

bul : {A : Tür} → Dizelge A → Doğal → Belki A
bul [] i = hiçbirşey
bul (x :: l) sıfır = sadece x
bul (x :: l) (ard i) = bul l i


-- Kendi uzunluğunu bilen Dizelge : Taşıyıcı
data Taşıyıcı (A : Tür) : Doğal → Tür where
  []   : Taşıyıcı A sıfır
  _::_ : {d : Doğal} → A → Taşıyıcı A d → Taşıyıcı A (ard d)


sıfırlar : (d : Doğal) → Taşıyıcı Doğal d
sıfırlar sıfır = []
sıfırlar (ard d) = 0 :: sıfırlar d

-- örtülü değişkenler işlev çağırılırken
-- verilmeyebilir.
öneEkle : {d : Doğal} → {T : Tür}
           → T → Taşıyıcı T d → Taşıyıcı T (ard d)
öneEkle t tler = t :: tler

-- (d - 1) (d - 2) .. 0 a kadar tüm doğal sayılardan oluşan
-- dizelgeyi üretir.
aşağı : (d : Doğal) → Taşıyıcı Doğal d
aşağı sıfır = []
aşağı (ard d) = d :: aşağı d

-- Taşıyıcıları birleştirme
birleştir : {A : Tür} {d e : Doğal}
             → Taşıyıcı A d → Taşıyıcı A e
             → Taşıyıcı A (d + e)
birleştir [] t2 = t2
birleştir (x :: t1) t2 = x :: (birleştir t1 t2)

-- Taşıyıcının ilk üyesini döner. Türünden dolayı boş
-- taşıyıcı durumunun işlev eşitliklerinde olması gerekmediğine
-- dikkat edelim.
baş : {T : Tür} {d : Doğal} → Taşıyıcı T (ard d) → T
baş (t :: tler) = t

-- Taşıyıcının ilk üyesi hariç kalan taşıyıcıyı döner.
kuyruk : {T : Tür} {d : Doğal} → Taşıyıcı T (ard d) → Taşıyıcı T d
kuyruk (t :: tler) = tler

-- İç çarpılacak iki taşıyıcının da aynı uzunlukta olması gerektiğinin
-- tür de belirtildiğine dikkat edelim.
içÇarpım : {d : Doğal} → Taşıyıcı Doğal d → Taşıyıcı Doğal d → Doğal
içÇarpım [] _ = sıfır
içÇarpım (t :: tler) (s :: sler) = (t × s) + (içÇarpım tler sler)

çarpım : Doğal
çarpım = içÇarpım (1 :: 2 :: 3 :: []) (4 :: 5 :: 6 :: [])

-- Sonlu doğal sayı kümesi. Sonlu d : 0 dan d - 1 e kadar olan
-- doğal sayıları içerir.
data Sonlu : Doğal → Tür where
  sıfır : {d : Doğal} → Sonlu (ard d)
  ard   : {d : Doğal} → Sonlu d → Sonlu (ard d)

sıfır3 : Sonlu 3
sıfır3 = sıfır

bir3 : Sonlu 3
bir3 = ard sıfır

iki3 : Sonlu 3
iki3 = ard (ard sıfır)

taşıBul : {T : Tür} {d : Doğal} → Taşıyıcı T d → Sonlu d → T
taşıBul (t :: tler) sıfır = t
taşıBul (t :: tler) (ard sıra) = taşıBul tler sıra

taşıKoy : {T : Tür} {d : Doğal} → Taşıyıcı T d → Sonlu d
                      → T → Taşıyıcı T d
taşıKoy (s :: tler) sıfır t = t :: tler
taşıKoy (s :: tler) (ard sıra) t =  s :: (taşıKoy tler sıra t)


-- Bağımlı çift türü.
data Σ (A : Tür) (B : A → Tür) : Tür where
  _,_ : (a : A) → B a → Σ A B

-- Bağımlı çift için bir başka isim tanımladık
_x'_ : (A B : Tür) → Tür
A x' B = Σ A (λ _ → B)

-- Bu iki işlev ilk bakışta anlamsız görünüyor olabilir
-- ama bir türden diğerine geçmeyi sağlıyor.
xçevirx' : {A B : Tür} → (A x B) → (A x' B)
xçevirx' (a , b) = (a , b)

x'çevirx : {A B : Tür}  → (A x' B) → (A x B)
x'çevirx (a , b) = (a , b)

ilkΣ : {A : Tür} {B : A → Tür} → Σ A B → A
ilkΣ (a , _) = a

ikinciΣ : {A : Tür} {B : A → Tür} → (z : Σ A B)  → B (ilkΣ z)
ikinciΣ (a , b) = b

Dizelge' : (A : Tür) → Tür
Dizelge' A = Σ Doğal (Taşıyıcı A)

[]' : {A : Tür} → Dizelge' A
[]' = sıfır , []

_::'_ : {A : Tür} → A → Dizelge' A → Dizelge' A
a ::' (d , alar) = ((ard d), a :: alar)

diz'çevirdiz : {A : Tür}  → Dizelge' A → Dizelge A
diz'çevirdiz (0 , []) = []
diz'çevirdiz ((ard d) , (a :: alar)) = a :: (diz'çevirdiz (d , alar))

dizçevirdiz' : {A : Tür} → Dizelge A → Dizelge' A
dizçevirdiz' [] = []'
dizçevirdiz' (a :: alar) = a ::' (dizçevirdiz' alar)


-- Dikkat edilirse, eğer dizelgenin uzunluğunu yanlış verirsek
-- tür doğrulanamayacaktır.
dizelge'1 : Dizelge' Doğruluk
dizelge'1 = (3 , doğru :: yanlış :: yanlış :: [])
-- dizelge1 = (2, doğru :: yanlış :: yanlış :: [])
-- tür doğrulamasından geçmeyecektir.

data Hangisi (A B : Tür) : Tür where
  sol : A → Hangisi A B
  sağ : B → Hangisi A B

seçenekler : {A B C : Tür} → Hangisi A B
              → (A → C) → (B → C) → C
seçenekler (sol a) k1 k2 = k1 a
seçenekler (sağ b) k1 k2 = k2 b

-- İlk bakışta doğru ve yanlış ile ⊤ ve ⊥ aynı şeylermiş gibi görünüyor.
-- Ama ilki bizim yarattığımız bir türün değerleri diğerleri ise kendileri türler.
-- Boolean mantığı ile Önermeler mantığı arasındaki fark.
data ⊤ : Tür where
  dd : ⊤

-- Boş tür, yanlış önermeleri temsil ediyor. Dikkat edilirse
-- kısmi işlevleri kabul eden Haskell gibi dillerde bu türleri
-- tanımlamak mümkün değildir. Tümcü Agda gibi dillerde münkündür.
data ⊥ : Tür where

-- Boş bir türden birey yaratmak mümkün olmadığından saçma deseni
-- kullanıyoruz ().
saçma : {A : Tür} → ⊥ → A
saçma ()

-- Önerme: P ise P, P → P
-- İşlev: Aynılık işlevi
kanıt1 : {P : Tür} → P → P
kanıt1 p = p

-- Önerme: Eğer ((P ise Q) ve (Q ise R)) ise P ise R
-- (P → Q) x (Q → R) → P → R
-- İşlev: Bileşik işlev.
-- Dikkat edilirse bunun işlev bileşke işlevinin serilmemiş
-- hali olduğu görülür.
kanıt2 : {P Q R : Tür} →  (P → Q) x (Q → R) → P → R
kanıt2 (f , g) = λ x → g (f x)

-- Önerme: Eğer ((P veya Q) ise R) ise (P ise R) ve (Q ise R)
-- (Hangisi P Q) → R → (P → R) x (Q → R)
kanıt3 : {P Q R : Tür} → (Hangisi P Q → R) → (P → R) x (Q → R)
kanıt3 işlv = ((λ h → işlv (sol h)) , λ h → işlv (sağ h))

-- Dışlanan orta kanununun çifte değilleme çevirisi kanıtı
garip : {P : Tür} → (Hangisi P (P → ⊥) → ⊥) → ⊥
garip h = h (sağ λ z → h (sol z))

-- Curry-Howard eşleşmesine göre önermeler tür olduğundan çift sayı
-- olma özelliğini bir tür olarak tanımlayabiliriz.
-- sıfır çift sayıdır ve eğer d çift ise d + 2 de çifttir.
data Çiftsayı : Doğal → Tür where
  sıfırÇift : Çiftsayı sıfır
  ardardÇift : {d : Doğal} → Çiftsayı d → Çiftsayı (ard (ard d))

6-çifttir : Çiftsayı 6
6-çifttir = ardardÇift (ardardÇift (ardardÇift sıfırÇift))

7-çift-değildir : Çiftsayı 7 → ⊥
7-çift-değildir (ardardÇift (ardardÇift (ardardÇift ())))

data Doğrumu : Doğruluk → Tür where
  DoğruDoğru : Doğrumu doğru

_=Doğal_ : Doğal → Doğal → Doğruluk
sıfır =Doğal sıfır = doğru
(ard a) =Doğal (ard b) = a =Doğal b
_ =Doğal _ = yanlış

-- Türdeki dizelgenin uzunluğu 3 değilse tür doğrulanmaz.
uzunluk-3 : Doğrumu (((1 :: 2 :: 3 :: []) uzunluk) =Doğal 3)
uzunluk-3 = DoğruDoğru

ikikatı : Doğal → Doğal
ikikatı sıfır = sıfır
ikikatı (ard d) = ard (ard (ikikatı d))

-- herhangi bir doğal sayının iki katının çift olduğunun kanıtı.
-- (evrensel kanıt)
ikikatı-çifttir : (d : Doğal) → Çiftsayı (ikikatı d)
ikikatı-çifttir sıfır = sıfırÇift
ikikatı-çifttir (ard d) = ardardÇift (ikikatı-çifttir d)

-- Herhangi bir doğal sayının kendine eşit olduğunun kanıtı.
-- (evrensel kanıt)
d-eşittir-d : (d : Doğal) → Doğrumu (d =Doğal d)
d-eşittir-d sıfır = DoğruDoğru
d-eşittir-d (ard d) = d-eşittir-d d

-- İki katının bir düzine, 12, olan bir doğal sayının var
-- olduğunun kanıtı. (Varoluşsal kanıt)
yarım-düzine : Σ Doğal (λ d → Doğrumu ((d + d) =Doğal 12))
yarım-düzine = 6 , DoğruDoğru

-- Her doğal sayı ya sıfırdır ya da başka bir doğal sayının
-- ardılıdır.
sıfır-veya-ardıl : (d : Doğal) →
        Hangisi (Doğrumu (d =Doğal sıfır))
                (Σ Doğal (λ e → Doğrumu (d =Doğal (ard e))))
sıfır-veya-ardıl sıfır = sol DoğruDoğru
sıfır-veya-ardıl (ard d) = sağ (d , d-eşittir-d d)

-- Aynılık türü. Aynılık işlevinin türü ile karıştırmamak gerekir.
-- yans "yasıma" nın kısaltılmış hali olarak düşünülmeli.
data _≡_ {A : Tür} : A → A → Tür where
  yans : {a : A} → a ≡ a

infix 4 _≡_

-- '1 + 1 = 2' önermesinin kanıtı. Öğretgede bunun Whitehead ve Russell'ın
-- ünlü kitapları 'Principia Mathematica' da 362. sayfada mümkün olabildiğini
-- burada ise 22. sayfada kanıtlanabildiğini söyleyerek eğleniyor.
bir-artı-bir : 1 + 1 ≡ 2
bir-artı-bir = yans

-- ve heyecan verici 0 1 e eşit değildir kanıtı.
sıfır-bir-değil : 0 ≡ 1 → ⊥
sıfır-bir-değil ()

-- Çok şekilli türlerin eşitliği ile ilgili kanıt.
aynı-girdiyi-döner : {A : Tür} → (a : A) → a aynı ≡ a
aynı-girdiyi-döner a = yans

-- Eşitliğin bakışlılık özelliğinin kanıtı.
bakş : {A : Tür} {a b : A} → a ≡ b → b ≡ a
bakş yans = yans

-- Eşitliğin geçişlilik özelliğinin kanıtı.
geçş : {A : Tür} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
geçş yans yans = yans

-- Eşitliğin kalandaşlık özelliği kanıtı.
kalandş : {A B : Tür} {a b : A} → (işlv : A → B)
            → a ≡ b → işlv a ≡ işlv b
kalandş işlv yans = yans

-- uzunluk işlevi için birim sınaması yazmak için bir kısayol.
-- Eğer herhangi bir şey değişir ve eşitlik sağlanmazsa
-- Agda tür taramasını başarılı sonlanmadığından hemen haberimiz
-- olacaktır. Ayrıca uzunluk işlevinin girdisini soldan
-- aldığı unutulmamalı izlek okunurken.
uzunluk-sınama-1 : (1 :: 2 :: []) uzunluk ≡ 2
uzunluk-sınama-1 = yans

-- Eşitliklerle akıl yürütme kanıtları için
-- gerekli yardımcı türler.
başla_ : {A : Tür} {a b : A} → a ≡ b → a ≡ b
başla k = k

_bitir : {A : Tür} → (a : A) → a ≡ a
k bitir = yans

_=⟨_⟩_ : {A : Tür} → (a : A) → {b c : A}
           → a ≡ b → b ≡ c → a ≡ c
a =⟨ k ⟩ l = geçş k l

_=⟨⟩_ : {A : Tür} → (a : A) → {b : A}
           → a ≡ b → a ≡ b
a =⟨⟩ k = a =⟨ yans ⟩ k

infix 1 başla_
infix 3 _bitir
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

[_] : {A : Tür} → A → Dizelge A
[ a ] = a :: []

tersi : {A : Tür} → Dizelge A → Dizelge A
tersi [] = []
tersi (a :: alar) = tersi alar ++ [ a ]

-- Tek üyeli dizelgenin tersinin aynı olduğunun kanıtı
teklinin-tersi : {A : Tür} (a : A) → tersi [ a ] ≡ [ a ]
teklinin-tersi a =
  başla  -- kanıta başla
    tersi [ a ]
  =⟨⟩ -- [_] nin tanımı
    tersi (a :: [])
  =⟨⟩ -- tersi nin ikinci eşitliğini uygula
    tersi [] ++ [ a ]
  =⟨⟩ -- tersi nin ilk eşitliğini uygula
    [] ++ [ a ]
  =⟨⟩ -- _++_ yi uygula
    [ a ]
  bitir  -- kanıtlandı

-- (d değil) değil = d önermesinin kanıtı. d : Doğruluk
değil-değil : (d : Doğruluk) → (d değil) değil ≡ d
değil-değil yanlış =
  başla
    (yanlış değil) değil
  =⟨⟩ -- içteki değilleme
    doğru değil
  =⟨⟩ -- değilleme
    yanlış
  bitir
değil-değil doğru =
  başla
    (doğru değil) değil
  =⟨⟩ -- içteki değilleme
    yanlış değil
  =⟨⟩ -- değilleme
    doğru
  bitir

-- d + 0 = d önermesinin kanıtı : Doğal
d-artı-0 : (d : Doğal) → d + 0 ≡ d
d-artı-0 sıfır =
  başla
    sıfır + sıfır
  =⟨⟩
    sıfır
  bitir
d-artı-0 (ard d) =
  başla
    (ard d) + sıfır
  =⟨⟩ -- + yı uyguluyoruz
    ard (d + sıfır)
  =⟨ kalandş ard (d-artı-0 d) ⟩ -- tüme varım varsayımını uyguluyoruz
    ard d
  bitir

-- d + ard e = ard (d + e)
topl-ard-ard-topl : (d e : Doğal) → d + ard e ≡ ard (d + e)
topl-ard-ard-topl sıfır e = yans
topl-ard-ard-topl (ard d) e =
  başla
    ard d + ard e
  =⟨⟩
    ard (d + (ard e))
  =⟨ kalandş ard (topl-ard-ard-topl d e) ⟩
    ard (ard (d + e))
  bitir

-- d + e = e + d
topl-değişme-özelliği : (d e : Doğal) → d + e ≡ e + d
topl-değişme-özelliği d sıfır =
  başla
    d + sıfır
  =⟨ d-artı-0 d ⟩ -- Yukarıda kanıtlanan savın kullanımı
    d
  =⟨⟩ -- _+_ tanımının tersine uygulanışı
    sıfır + d
  bitir
topl-değişme-özelliği d (ard e) =
  başla
    d + (ard e)
  =⟨ topl-ard-ard-topl d e ⟩
    ard (d + e)
  =⟨ kalandş ard (topl-değişme-özelliği d e) ⟩
    ard (e + d)
  =⟨⟩ -- _+_ tanımının tersine uygulanışı
    (ard e) + d
  bitir

toplama-birleşme-özelliği : (a b c : Doğal)
                             → a + (b + c) ≡ (a + b) + c
toplama-birleşme-özelliği sıfır b c =
  başla
    sıfır + (b + c)
  =⟨⟩
    b + c
  =⟨⟩
    (sıfır + b) + c
  bitir
toplama-birleşme-özelliği (ard a) b c =
  başla
    (ard a) + (b + c)
  =⟨⟩
    ard (a + (b + c))
  =⟨ kalandş ard (toplama-birleşme-özelliği a b c) ⟩
    ard ((a + b) + c)
  =⟨⟩
    ard (a + b) + c
  =⟨⟩
    ((ard a) + b) + c
  bitir

-- Herhangi bir A türünden veriyi d kadar çoğaltıp
-- dizelge dönen işlev.
_çoğalt_ : {A : Tür} → (d : Doğal) → (a : A)  → Dizelge A
sıfır çoğalt a = []
ard d çoğalt a = a :: (d çoğalt a)

-- a çoğalt d nin uzunluğunun her zaman d olduğunun kanıtı.
a-çoğalt-d-uzunluk-herzaman-d : {A : Tür} → (d : Doğal) → (a : A)
                                 → (d çoğalt a) uzunluk ≡ d
a-çoğalt-d-uzunluk-herzaman-d sıfır a = yans
a-çoğalt-d-uzunluk-herzaman-d (ard d) a =
  başla
    ((ard d) çoğalt a) uzunluk
  =⟨ kalandş ard (a-çoğalt-d-uzunluk-herzaman-d d a) ⟩
    (ard d)
  bitir


ekle-[] : {A : Tür} → (diz : Dizelge A) → diz ++ [] ≡ diz
ekle-[] [] = yans
ekle-[] (a :: alar) =
  başla
    (a :: alar) ++ []
  =⟨ kalandş (a ::_) (ekle-[] alar) ⟩
    (a :: alar)
  bitir

ekle-birleşme-özelliği : {A : Tür} → (a b c : Dizelge A)
                          → (a ++ b) ++ c ≡ a ++ (b ++ c)
ekle-birleşme-özelliği [] b c =
  başla
    ([] ++ b) ++ c
  =⟨⟩
    b ++ c
  =⟨⟩
    [] ++ (b ++ c)
  bitir
ekle-birleşme-özelliği (d :: dler) b c =
  başla
    ((d :: dler) ++ b) ++ c
  =⟨⟩
    (d :: (dler ++ b)) ++ c
  =⟨⟩
    ([ d ] ++ (dler ++ b)) ++ c
  =⟨ kalandş  ([ d ] ++_) (ekle-birleşme-özelliği dler b c) ⟩
    [ d ] ++ (dler ++ (b ++ c))
  =⟨⟩
    ([ d ] ++ dler) ++ (b ++ c)
  =⟨⟩
    (d :: dler) ++ ( b ++ c)
  bitir

-- Bir dizelgenin tersinin tersi kendisidir.
tersinin-tersi : {A : Tür} → (diz : Dizelge A)
                  → tersi (tersi diz) ≡ diz
tersinin-tersi [] = yans
tersinin-tersi (a :: alar) =
  başla
    tersi (tersi (a :: alar))
  =⟨⟩
    tersi (tersi alar ++ [ a ])
  =⟨ tersi-dağılım-özelliği (tersi alar) [ a ] ⟩
    tersi [ a ] ++ tersi (tersi alar)
  =⟨⟩
    [ a ] ++ tersi (tersi alar)
  =⟨⟩
    a :: tersi (tersi alar)
  =⟨ kalandş (a ::_) (tersinin-tersi alar) ⟩
    a :: alar
  bitir
  where
    tersi-dağılım-özelliği : {A : Tür} → (alar bler : Dizelge A)
                                    → tersi (alar ++ bler) ≡ tersi bler ++ tersi alar
    tersi-dağılım-özelliği [] bler =
      başla
        tersi ([] ++ bler)
      =⟨⟩
        tersi bler
      =⟨ bakş (ekle-[] (tersi bler)) ⟩
        tersi bler ++ []
      =⟨⟩
        tersi bler ++ tersi []
      bitir
    tersi-dağılım-özelliği (a :: alar) bler =
      başla
        tersi ((a :: alar) ++ bler)
      =⟨⟩
        tersi (a :: (alar ++ bler))
      =⟨⟩
        tersi (alar ++ bler) ++ tersi [ a ]
      =⟨⟩
        tersi (alar ++ bler) ++ [ a ]
      =⟨ kalandş (_++ [ a ]) (tersi-dağılım-özelliği alar bler) ⟩
        (tersi bler ++ tersi alar) ++ [ a ]
      =⟨ ekle-birleşme-özelliği (tersi bler) (tersi alar) [ a ] ⟩
        tersi bler ++ (tersi alar ++ [ a ])
      =⟨⟩
        tersi bler ++ tersi (a :: alar)
      bitir

-- eşle işlevinin 2 işlevge yasasına uyduğunun kanıtı
-- 1. eşle aynı = aynı
-- 2. eşle (i ∘ j) = eşle i ∘ eşle j
-- ∘ : işlev bileşkesi

-- eşle d aynı ≡ d
eşle-aynı : {A : Tür} (d : Dizelge A) → eşle d _aynı ≡ d
eşle-aynı [] =
  başla
    eşle [] _aynı
  =⟨⟩
    [] aynı
  =⟨⟩
    []
  bitir
eşle-aynı (a :: alar) =
  başla
    eşle (a :: alar) _aynı
  =⟨⟩
    (a aynı) :: (eşle alar _aynı)
  =⟨⟩
    a :: (eşle alar _aynı)
  =⟨ kalandş (a ::_) (eşle-aynı alar) ⟩
    (a :: alar)
  bitir

-- İşlev bileşkesi tanımı
_∘_ : {A B C : Tür} → (B → C) → (A → B) → (A → C)
g ∘ h = λ x → g(h(x))

-- eşle (i ∘ j) ≡ eşle i ∘ eşle j
eşle-bileşke : {A B C : Tür} → (f : B → C) → (g : A → B)
                → (d : Dizelge A)
                → eşle d (f ∘ g) ≡ eşle (eşle d g) f
eşle-bileşke f g [] =
  başla
    eşle [] (f ∘ g)
  =⟨⟩
    []
  =⟨⟩
    eşle [] f
  =⟨⟩
   eşle (eşle [] g) f
  bitir
eşle-bileşke f g (a :: alar) =
  başla
    eşle (a :: alar) (f ∘ g)
  =⟨⟩
    ((f ∘ g) a) :: eşle alar (f ∘ g)
  =⟨⟩
    f(g a) :: eşle alar (f ∘ g)
  =⟨ kalandş (f (g a) ::_) (eşle-bileşke f g alar) ⟩
    f(g a) :: eşle (eşle alar g) f
  =⟨⟩
    eşle (g a :: eşle alar g) f
  =⟨⟩
    eşle (eşle (a :: alar) g) f
  bitir

-- (eşle d f) uzunluk ≡ d uzunluk kanıtı
eşle-uzunluk-eşit : {K L : Tür} → (d : Dizelge K)
                     → (f : K → L)
                     → (eşle d f) uzunluk ≡ d uzunluk
eşle-uzunluk-eşit [] f = yans
eşle-uzunluk-eşit (a :: alar) f =
  başla
    (eşle (a :: alar) f) uzunluk
  =⟨⟩
    ((f a) :: (eşle alar f)) uzunluk
  =⟨⟩
    1 + ((eşle alar f) uzunluk)
  =⟨ kalandş (1 +_) (eşle-uzunluk-eşit alar f) ⟩
    1 + (alar uzunluk)
  =⟨⟩
    (a :: alar) uzunluk
  bitir

-- Dizelgenin önünden istenen kadar alıp yeni bir dizelge döner.
_den_al : {A : Tür} → (diz : Dizelge A) → (d : Doğal) → Dizelge A
[] den d al = []
(a :: alar) den sıfır al = []
(a :: alar) den (ard d) al = a :: (alar den d al)

-- Dizelgenin önünden istenen kadar atıp yeni bir dizelge döner.
_den_at : {A : Tür} → (diz : Dizelge A) → (d : Doğal) → Dizelge A
[] den d at = []
(a :: alar) den sıfır at = (a :: alar)
(a :: alar) den (ard d) at = alar den d at

-- (diz den d al) ++ (diz den d at) ≡ d kanıtı
al-ekle-at-eşit : {A : Tür} → (diz : Dizelge A) → (d : Doğal)
                   → (diz den d al) ++ (diz den d at) ≡ diz
al-ekle-at-eşit [] d = yans
al-ekle-at-eşit (a :: alar) sıfır = yans
al-ekle-at-eşit (a :: alar) (ard d) =
  başla
    ((a :: alar) den (ard d) al) ++ ((a :: alar) den (ard d) at)
  =⟨⟩
    (a :: (alar den d al)) ++ (alar den d at)
  =⟨⟩
    a :: ((alar den d al) ++ (alar den d at))
  =⟨ kalandş (a ::_) (al-ekle-at-eşit alar d) ⟩
    a :: alar
  bitir

-- tersi işlevinin daha hızlı ve karmaşıklığı O(n²)
-- olan ++ işlevi yerine doğrusal olan başka bir
-- yardımcı işlev kullanan sürümü
tersi-birikim : {A : Tür} → Dizelge A → Dizelge A
                 → Dizelge A
tersi-birikim [] alar = alar
tersi-birikim (a :: alar) diza = tersi-birikim alar (a :: diza)

tersi' : {A : Tür} → Dizelge A → Dizelge A
tersi' diz = tersi-birikim diz []

-- tersi ve tersi' işlevlerinin aynı işleve sahip
-- olduğunun kanıtı
tersi-tersi' : {A : Tür} → (diz : Dizelge A)
                → tersi' diz ≡ tersi diz
tersi-tersi' diz =
  başla
    tersi' diz
  =⟨⟩
    tersi-birikim diz []
  =⟨ tersi-birikim-önsav diz [] ⟩
    tersi diz ++ []
  =⟨ ekle-[] (tersi diz) ⟩
    tersi diz
  bitir
  where
    tersi-birikim-önsav : {A : Tür} → (diz1 diz2 : Dizelge A)
                           → tersi-birikim diz1 diz2 ≡ tersi diz1 ++ diz2
    tersi-birikim-önsav [] diz2 =
      başla
        tersi-birikim [] diz2
      =⟨⟩
        diz2
      =⟨⟩
        [] ++ diz2
      =⟨⟩
        (tersi []) ++ diz2
      bitir
    tersi-birikim-önsav (a :: alar) diz =
      başla
        tersi-birikim (a :: alar) diz
      =⟨⟩
        tersi-birikim alar (a :: diz)
      =⟨ tersi-birikim-önsav alar (a :: diz) ⟩
        tersi alar ++ (a :: diz)
      =⟨⟩
        tersi alar ++ ([ a ] ++ diz)
      =⟨ bakş (ekle-birleşme-özelliği (tersi alar) [ a ] diz) ⟩
        (tersi alar ++ [ a ]) ++ diz
      =⟨⟩
        tersi (a :: alar) ++ diz
      bitir
