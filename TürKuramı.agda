module TürKuramı where

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

  -- Bu pragma sayesinde tanımladığımız Doğal
  -- türümüz Agda'nın kendi eşlenik türü ile
  -- ilişkilendiriliyor ki normal rakamlar ile
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


  -- Dikkat edilirse, eğer Listenin uzunluğunu yanlış verirsek
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
  kanıt2 : {P Q R : Tür} →  (P → Q) x (Q → R) → P → R
  kanıt2 (f , g) = λ x → g (f x)
