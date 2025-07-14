(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort K 0)
(declare-sort N 0)
(declare-sort PN 0)
(declare-sort PNN 0)
(declare-sort PNZ 0)
(declare-fun MS (N Int PNZ) Bool)
(declare-fun MS0 (N N PNN) Bool)
(declare-fun MS1 (N PN) Bool)
(declare-fun b () PN)
(declare-fun c () PNN)
(declare-fun f () PNN)
(declare-fun g () PNN)
(declare-fun h () PNN)
(declare-fun ko () K)
(declare-fun lft () PN)
(declare-fun lt () PNN)
(declare-fun n () K)
(declare-fun nil () N)
(declare-fun ok () K)
(declare-fun p () N)
(declare-fun q () N)
(declare-fun rht () PN)
(declare-fun rt () PNN)
(declare-fun t () N)
(declare-fun ult () PNN)
(declare-fun urt () PNN)
(declare-fun vlt () PNN)
(declare-fun vrt () PNN)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x323 N) (x324 N)) 
            (exists ((X PNN)) 
                (and 
                    (MS0 x323 x324 X) 
                    (forall ((y2 N) (y3 N)) 
                        (=> 
                            (MS0 y2 y3 X) 
                            (and 
                                (= y2 x323) 
                                (= y3 x324))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x325 N) (x326 Int)) 
            (exists ((X0 PNZ)) 
                (and 
                    (MS x325 x326 X0) 
                    (forall ((y4 N) (y5 Int)) 
                        (=> 
                            (MS y4 y5 X0) 
                            (and 
                                (= y4 x325) 
                                (= y5 x326))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x327 N)) 
            (exists ((X1 PN)) 
                (and 
                    (MS1 x327 X1) 
                    (forall ((y6 N)) 
                        (=> 
                            (MS1 y6 X1) 
                            (= y6 x327)))))))
(assert (! (forall ((a Int)) 
               (exists ((b0 Int) (f0 PNZ)) 
                   (and 
                       (forall ((x N) (x0 Int)) 
                           (=> 
                               (MS x x0 f0) 
                               (and 
                                   (<= a x0) 
                                   (<= x0 b0)))) 
                       (forall ((x1 N) (x2 Int) (x3 Int)) 
                           (=> 
                               (and 
                                   (MS x1 x2 f0) 
                                   (MS x1 x3 f0)) 
                               (= x2 x3))) 
                       (forall ((x4 N)) 
                           (exists ((x5 Int)) 
                               (MS x4 x5 f0))) 
                       (forall ((x6 Int) (x7 N) (x8 N)) 
                           (=> 
                               (and 
                                   (MS x7 x6 f0) 
                                   (MS x8 x6 f0)) 
                               (= x7 x8))))))
         :named hyp1))
(assert (! (forall ((x9 N) (x10 N)) 
               (=> 
                   (= x9 x10) 
                   (MS0 x9 x10 c)))
         :named hyp2))
(assert (! (forall ((x11 N) (x12 N)) 
               (=> 
                   (exists ((x13 N)) 
                       (and 
                           (MS0 x11 x13 c) 
                           (MS0 x13 x12 g))) 
                   (MS0 x11 x12 c)))
         :named hyp3))
(assert (! (forall ((r PNN)) 
               (=> 
                   (and 
                       (forall ((x14 N) (x15 N)) 
                           (=> 
                               (= x14 x15) 
                               (MS0 x14 x15 r))) 
                       (forall ((x16 N) (x17 N)) 
                           (=> 
                               (exists ((x18 N)) 
                                   (and 
                                       (MS0 x16 x18 r) 
                                       (MS0 x18 x17 g))) 
                               (MS0 x16 x17 r)))) 
                   (forall ((x19 N) (x20 N)) 
                       (=> 
                           (MS0 x19 x20 c) 
                           (MS0 x19 x20 r)))))
         :named hyp4))
(assert (! (forall ((x21 N) (x22 N) (x23 N)) 
               (=> 
                   (and 
                       (MS0 x21 x22 lt) 
                       (MS0 x21 x23 lt)) 
                   (= x22 x23)))
         :named hyp5))
(assert (! (forall ((x24 N) (x25 N) (x26 N)) 
               (=> 
                   (and 
                       (MS0 x24 x25 rt) 
                       (MS0 x24 x26 rt)) 
                   (= x25 x26)))
         :named hyp6))
(assert (! (forall ((x27 N) (x28 N)) 
               (= 
                   (MS0 x27 x28 g) 
                   (or 
                       (MS0 x27 x28 lt) 
                       (MS0 x27 x28 rt))))
         :named hyp7))
(assert (! (MS1 t b)
         :named hyp8))
(assert (! (=> 
               (forall ((x29 N)) 
                   (=> 
                       (exists ((x30 N)) 
                           (and 
                               (MS1 x30 b) 
                               (MS0 x30 x29 g))) 
                       (MS1 x29 b))) 
               (forall ((x31 N)) 
                   (=> 
                       (exists ((x32 N)) 
                           (and 
                               (MS1 x32 b) 
                               (MS0 x32 x31 c))) 
                       (MS1 x31 b))))
         :named hyp9))
(assert (! (forall ((x33 N)) 
               (=> 
                   (MS1 x33 b) 
                   (exists ((x34 N)) 
                       (and 
                           (= x34 t) 
                           (MS0 x34 x33 c)))))
         :named hyp10))
(assert (! (MS1 p b)
         :named hyp11))
(assert (! (and 
               (forall ((x35 N) (x36 N)) 
                   (=> 
                       (MS0 x35 x36 f) 
                       (and 
                           (MS1 x35 b) 
                           (not 
                               (= x35 t)) 
                           (MS1 x36 b) 
                           (not 
                               (= x36 p))))) 
               (forall ((x37 N) (x38 N) (x39 N)) 
                   (=> 
                       (and 
                           (MS0 x37 x38 f) 
                           (MS0 x37 x39 f)) 
                       (= x38 x39))) 
               (forall ((x40 N) (x41 N) (x42 N)) 
                   (=> 
                       (and 
                           (MS0 x41 x40 f) 
                           (MS0 x42 x40 f)) 
                       (= x41 x42))))
         :named hyp12))
(assert (! (forall ((x43 N)) 
               (= 
                   (or 
                       (exists ((x44 N)) 
                           (MS0 x43 x44 f)) 
                       (= x43 t)) 
                   (or 
                       (exists ((x45 N)) 
                           (MS0 x45 x43 f)) 
                       (= x43 p))))
         :named hyp13))
(assert (! (forall ((s PN)) 
               (=> 
                   (and 
                       (forall ((x46 N)) 
                           (=> 
                               (MS1 x46 s) 
                               (or 
                                   (exists ((x47 N)) 
                                       (MS0 x46 x47 f)) 
                                   (= x46 t)))) 
                       (forall ((x48 N)) 
                           (=> 
                               (MS1 x48 s) 
                               (exists ((x49 N)) 
                                   (and 
                                       (MS1 x49 s) 
                                       (MS0 x48 x49 f)))))) 
                   (forall ((x50 N)) 
                       (not 
                           (MS1 x50 s)))))
         :named hyp14))
(assert (! (forall ((x51 N) (x52 N)) 
               (=> 
                   (MS0 x52 x51 f) 
                   (MS0 x51 x52 g)))
         :named hyp15))
(assert (! (forall ((x53 N)) 
               (=> 
                   (exists ((x54 N)) 
                       (and 
                           (MS1 x54 b) 
                           (not 
                               (or 
                                   (exists ((x55 N)) 
                                       (MS0 x54 x55 f)) 
                                   (= x54 t))) 
                           (MS0 x54 x53 g))) 
                   (MS1 x53 b)))
         :named hyp16))
(assert (! (=> 
               (= n ok) 
               (forall ((x56 N)) 
                   (=> 
                       (exists ((x57 N)) 
                           (and 
                               (MS1 x57 b) 
                               (MS0 x57 x56 g))) 
                       (MS1 x56 b))))
         :named hyp17))
(assert (! (=> 
               (= n ok) 
               (= p t))
         :named hyp18))
(assert (! (=> 
               (= p t) 
               (forall ((x58 N) (x59 N)) 
                   (not 
                       (MS0 x58 x59 f))))
         :named hyp19))
(assert (! (=> 
               (forall ((x60 N) (x61 N)) 
                   (not 
                       (MS0 x60 x61 f))) 
               (= p t))
         :named hyp20))
(assert (! (forall ((x62 N)) 
               (= 
                   (or 
                       (MS1 x62 lft) 
                       (MS1 x62 rht)) 
                   (exists ((x63 N)) 
                       (MS0 x63 x62 f))))
         :named hyp21))
(assert (! (forall ((x64 N)) 
               (not 
                   (and 
                       (MS1 x64 lft) 
                       (MS1 x64 rht))))
         :named hyp22))
(assert (! (forall ((x65 N) (x66 N)) 
               (=> 
                   (and 
                       (MS0 x66 x65 f) 
                       (MS1 x65 lft)) 
                   (MS0 x65 x66 lt)))
         :named hyp23))
(assert (! (forall ((x67 N) (x68 N)) 
               (=> 
                   (and 
                       (MS0 x68 x67 f) 
                       (MS1 x67 rht)) 
                   (MS0 x67 x68 rt)))
         :named hyp24))
(assert (! (=> 
               (forall ((x69 N) (x70 N)) 
                   (not 
                       (MS0 x69 x70 f))) 
               (and 
                   (forall ((x71 N)) 
                       (not 
                           (MS1 x71 lft))) 
                   (forall ((x72 N)) 
                       (not 
                           (MS1 x72 rht)))))
         :named hyp25))
(assert (! (=> 
               (= n ok) 
               (forall ((x73 N) (x74 N)) 
                   (not 
                       (MS0 x73 x74 f))))
         :named hyp26))
(assert (! (=> 
               (= n ok) 
               (and 
                   (forall ((x75 N)) 
                       (not 
                           (MS1 x75 lft))) 
                   (forall ((x76 N)) 
                       (not 
                           (MS1 x76 rht)))))
         :named hyp27))
(assert (! (forall ((x77 N) (x78 N)) 
               (= 
                   (MS0 x77 x78 ult) 
                   (or 
                       (and 
                           (MS0 x77 x78 lt) 
                           (not 
                               (MS1 x77 lft))) 
                       (and 
                           (MS0 x77 x78 f) 
                           (MS1 x77 lft)))))
         :named hyp28))
(assert (! (forall ((x79 N) (x80 N) (x81 N)) 
               (=> 
                   (and 
                       (MS0 x79 x80 ult) 
                       (MS0 x79 x81 ult)) 
                   (= x80 x81)))
         :named hyp29))
(assert (! (forall ((x82 N) (x83 N)) 
               (= 
                   (MS0 x82 x83 urt) 
                   (or 
                       (and 
                           (MS0 x82 x83 rt) 
                           (not 
                               (MS1 x82 rht))) 
                       (and 
                           (MS0 x82 x83 f) 
                           (MS1 x82 rht)))))
         :named hyp30))
(assert (! (forall ((x84 N) (x85 N) (x86 N)) 
               (=> 
                   (and 
                       (MS0 x84 x85 urt) 
                       (MS0 x84 x86 urt)) 
                   (= x85 x86)))
         :named hyp31))
(assert (! (forall ((x87 N) (x88 N)) 
               (= 
                   (MS0 x87 x88 h) 
                   (and 
                       (MS0 x87 x88 f) 
                       (= x87 p))))
         :named hyp32))
(assert (! (=> 
               (= n ok) 
               (forall ((x89 N) (x90 N)) 
                   (= 
                       (MS0 x89 x90 ult) 
                       (MS0 x89 x90 lt))))
         :named hyp33))
(assert (! (=> 
               (= n ok) 
               (forall ((x91 N) (x92 N)) 
                   (= 
                       (MS0 x91 x92 urt) 
                       (MS0 x91 x92 rt))))
         :named hyp34))
(assert (! (forall ((x93 N) (x94 N)) 
               (= 
                   (MS0 x93 x94 vlt) 
                   (or 
                       (and 
                           (MS0 x93 x94 ult) 
                           (not 
                               (exists ((x95 N)) 
                                   (and 
                                       (= x93 t) 
                                       (= x95 nil) 
                                       (MS1 x93 lft))))) 
                       (and 
                           (= x93 t) 
                           (= x94 nil) 
                           (MS1 x93 lft)))))
         :named hyp35))
(assert (! (forall ((x96 N) (x97 N) (x98 N)) 
               (=> 
                   (and 
                       (MS0 x96 x97 vlt) 
                       (MS0 x96 x98 vlt)) 
                   (= x97 x98)))
         :named hyp36))
(assert (! (forall ((x99 N) (x100 N)) 
               (= 
                   (MS0 x99 x100 vrt) 
                   (or 
                       (and 
                           (MS0 x99 x100 urt) 
                           (not 
                               (exists ((x101 N)) 
                                   (and 
                                       (= x99 t) 
                                       (= x101 nil) 
                                       (MS1 x99 rht))))) 
                       (and 
                           (= x99 t) 
                           (= x100 nil) 
                           (MS1 x99 rht)))))
         :named hyp37))
(assert (! (forall ((x102 N) (x103 N) (x104 N)) 
               (=> 
                   (and 
                       (MS0 x102 x103 vrt) 
                       (MS0 x102 x104 vrt)) 
                   (= x103 x104)))
         :named hyp38))
(assert (! (=> 
               (= p t) 
               (= q nil))
         :named hyp39))
(assert (! (=> 
               (= n ok) 
               (forall ((x105 N) (x106 N)) 
                   (= 
                       (MS0 x105 x106 vlt) 
                       (MS0 x105 x106 lt))))
         :named hyp40))
(assert (! (=> 
               (= n ok) 
               (forall ((x107 N) (x108 N)) 
                   (= 
                       (MS0 x107 x108 vrt) 
                       (MS0 x107 x108 rt))))
         :named hyp41))
(assert (! (= n ko)
         :named hyp42))
(assert (! (forall ((x109 N)) 
               (=> 
                   (exists ((x110 N)) 
                       (and 
                           (= x110 p) 
                           (MS0 x110 x109 vlt))) 
                   (MS1 x109 b)))
         :named hyp43))
(assert (! (exists ((x111 N)) 
               (MS0 p x111 vrt))
         :named hyp44))
(assert (! (exists ((x112 N)) 
               (MS0 p x112 urt))
         :named hyp45))
(assert (! (forall ((x113 K)) 
               (or 
                   (= x113 ok) 
                   (= x113 ko)))
         :named hyp46))
(assert (! (not 
               (= ok ko))
         :named hyp47))
(assert (! (not 
               (or 
                   (exists ((x114 N)) 
                       (MS0 nil x114 lt)) 
                   (exists ((x115 N)) 
                       (MS0 nil x115 rt))))
         :named hyp48))
(assert (! (not 
               (or 
                   (exists ((x116 N)) 
                       (MS0 x116 nil lt)) 
                   (exists ((x117 N)) 
                       (MS0 x117 nil rt))))
         :named hyp49))
(assert (! (or 
               (forall ((x118 N)) 
                   (=> 
                       (exists ((x119 N)) 
                           (and 
                               (MS1 x119 b) 
                               (MS0 x119 x118 g))) 
                       (MS1 x118 b))) 
               (and 
                   (not 
                       (forall ((x120 N)) 
                           (=> 
                               (exists ((x121 N)) 
                                   (and 
                                       (MS1 x121 b) 
                                       (MS0 x121 x120 g))) 
                               (MS1 x120 b)))) 
                   (exists ((x122 N) (y N)) 
                       (and 
                           (MS0 x122 y g) 
                           (MS1 x122 b) 
                           (not 
                               (MS1 y b))))))
         :named hyp50))
(assert (! (=> 
               (not 
                   (= p t)) 
               (exists ((x123 N)) 
                   (MS0 p x123 f)))
         :named hyp51))
(assert (! (=> 
               (and 
                   (not 
                       (= p t)) 
                   (MS0 p t f)) 
               (forall ((x124 N) (x125 N)) 
                   (= 
                       (MS0 x124 x125 f) 
                       (and 
                           (= x124 p) 
                           (= x125 t)))))
         :named hyp52))
(assert (! (=> 
               (not 
                   (= p t)) 
               (and 
                   (exists ((x126 N)) 
                       (MS0 p x126 f)) 
                   (forall ((x127 N) (x128 N) (x129 N)) 
                       (=> 
                           (and 
                               (MS0 x127 x128 f) 
                               (MS0 x127 x129 f)) 
                           (= x128 x129)))))
         :named hyp53))
(assert (! (not 
               (MS1 p lft))
         :named hyp54))
(assert (! (not 
               (MS1 p rht))
         :named hyp55))
(assert (! (=> 
               (not 
                   (= p t)) 
               (or 
                   (exists ((x130 N)) 
                       (and 
                           (MS0 p x130 h) 
                           (MS1 x130 lft))) 
                   (exists ((x131 N)) 
                       (and 
                           (MS0 p x131 h) 
                           (MS1 x131 rht)))))
         :named hyp56))
(assert (! (=> 
               (not 
                   (= p t)) 
               (and 
                   (exists ((x132 N)) 
                       (MS0 p x132 h)) 
                   (forall ((x133 N) (x134 N) (x135 N)) 
                       (=> 
                           (and 
                               (MS0 x133 x134 h) 
                               (MS0 x133 x135 h)) 
                           (= x134 x135)))))
         :named hyp57))
(assert (! (=> 
               (not 
                   (= p t)) 
               (MS0 p q h))
         :named hyp58))
(assert (! (=> 
               (not 
                   (= p t)) 
               (or 
                   (MS1 q lft) 
                   (MS1 q rht)))
         :named hyp59))
(assert (! (not 
               (forall ((x136 N)) 
                   (=> 
                       (exists ((x137 N)) 
                           (and 
                               (= x137 p) 
                               (MS0 x137 x136 vrt))) 
                       (MS1 x136 b))))
         :named hyp60))
(assert (! (or 
               (and 
                   (not 
                       (forall ((x138 N)) 
                           (=> 
                               (exists ((x139 N)) 
                                   (and 
                                       (= x139 p) 
                                       (MS0 x139 x138 g))) 
                               (MS1 x138 b)))) 
                   (exists ((y0 N)) 
                       (and 
                           (MS0 p y0 g) 
                           (not 
                               (MS1 y0 b))))) 
               (and 
                   (forall ((x140 N)) 
                       (=> 
                           (exists ((x141 N)) 
                               (and 
                                   (= x141 p) 
                                   (MS0 x141 x140 g))) 
                           (MS1 x140 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x142 N)) 
                       (=> 
                           (exists ((x143 N)) 
                               (and 
                                   (= x143 p) 
                                   (MS0 x143 x142 g))) 
                           (MS1 x142 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp61))
(assert (! (or 
               (not 
                   (forall ((x144 N)) 
                       (=> 
                           (exists ((x145 N)) 
                               (and 
                                   (= x145 p) 
                                   (MS0 x145 x144 lt))) 
                           (MS1 x144 b)))) 
               (and 
                   (forall ((x146 N)) 
                       (=> 
                           (exists ((x147 N)) 
                               (and 
                                   (= x147 p) 
                                   (MS0 x147 x146 lt))) 
                           (MS1 x146 b))) 
                   (not 
                       (forall ((x148 N)) 
                           (=> 
                               (exists ((x149 N)) 
                                   (and 
                                       (= x149 p) 
                                       (MS0 x149 x148 rt))) 
                               (MS1 x148 b))))) 
               (and 
                   (forall ((x150 N)) 
                       (=> 
                           (exists ((x151 N)) 
                               (and 
                                   (= x151 p) 
                                   (MS0 x151 x150 lt))) 
                           (MS1 x150 b))) 
                   (forall ((x152 N)) 
                       (=> 
                           (exists ((x153 N)) 
                               (and 
                                   (= x153 p) 
                                   (MS0 x153 x152 rt))) 
                           (MS1 x152 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x154 N)) 
                       (=> 
                           (exists ((x155 N)) 
                               (and 
                                   (= x155 p) 
                                   (MS0 x155 x154 lt))) 
                           (MS1 x154 b))) 
                   (forall ((x156 N)) 
                       (=> 
                           (exists ((x157 N)) 
                               (and 
                                   (= x157 p) 
                                   (MS0 x157 x156 rt))) 
                           (MS1 x156 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp62))
(assert (! (or 
               (not 
                   (forall ((x158 N)) 
                       (=> 
                           (exists ((x159 N)) 
                               (and 
                                   (= x159 p) 
                                   (MS0 x159 x158 lt))) 
                           (MS1 x158 b)))) 
               (and 
                   (forall ((x160 N)) 
                       (=> 
                           (exists ((x161 N)) 
                               (and 
                                   (= x161 p) 
                                   (MS0 x161 x160 lt))) 
                           (MS1 x160 b))) 
                   (not 
                       (forall ((x162 N)) 
                           (=> 
                               (exists ((x163 N)) 
                                   (and 
                                       (= x163 p) 
                                       (MS0 x163 x162 rt))) 
                               (MS1 x162 b))))) 
               (and 
                   (forall ((x164 N)) 
                       (=> 
                           (exists ((x165 N)) 
                               (and 
                                   (= x165 p) 
                                   (MS0 x165 x164 lt))) 
                           (MS1 x164 b))) 
                   (forall ((x166 N)) 
                       (=> 
                           (exists ((x167 N)) 
                               (and 
                                   (= x167 p) 
                                   (MS0 x167 x166 rt))) 
                           (MS1 x166 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x168 N)) 
                       (and 
                           (MS0 p x168 f) 
                           (MS1 x168 lft)))) 
               (and 
                   (forall ((x169 N)) 
                       (=> 
                           (exists ((x170 N)) 
                               (and 
                                   (= x170 p) 
                                   (MS0 x170 x169 lt))) 
                           (MS1 x169 b))) 
                   (forall ((x171 N)) 
                       (=> 
                           (exists ((x172 N)) 
                               (and 
                                   (= x172 p) 
                                   (MS0 x172 x171 rt))) 
                           (MS1 x171 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x173 N)) 
                       (and 
                           (MS0 p x173 f) 
                           (MS1 x173 rht)))) 
               (and 
                   (forall ((x174 N)) 
                       (=> 
                           (exists ((x175 N)) 
                               (and 
                                   (= x175 p) 
                                   (MS0 x175 x174 lt))) 
                           (MS1 x174 b))) 
                   (forall ((x176 N)) 
                       (=> 
                           (exists ((x177 N)) 
                               (and 
                                   (= x177 p) 
                                   (MS0 x177 x176 rt))) 
                           (MS1 x176 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp63))
(assert (! (or 
               (not 
                   (forall ((x178 N)) 
                       (=> 
                           (exists ((x179 N)) 
                               (and 
                                   (= x179 p) 
                                   (MS0 x179 x178 lt))) 
                           (MS1 x178 b)))) 
               (and 
                   (forall ((x180 N)) 
                       (=> 
                           (exists ((x181 N)) 
                               (and 
                                   (= x181 p) 
                                   (MS0 x181 x180 lt))) 
                           (MS1 x180 b))) 
                   (not 
                       (forall ((x182 N)) 
                           (=> 
                               (exists ((x183 N)) 
                                   (and 
                                       (= x183 p) 
                                       (MS0 x183 x182 rt))) 
                               (MS1 x182 b))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x184 N)) 
                               (=> 
                                   (exists ((x185 N)) 
                                       (and 
                                           (= x185 p) 
                                           (MS0 x185 x184 lt))) 
                                   (MS1 x184 b))) 
                           (forall ((x186 N)) 
                               (=> 
                                   (exists ((x187 N)) 
                                       (and 
                                           (= x187 p) 
                                           (MS0 x187 x186 rt))) 
                                   (MS1 x186 b))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x188 N)) 
                               (MS0 p x188 f)) 
                           (forall ((x189 N) (x190 N) (x191 N)) 
                               (=> 
                                   (and 
                                       (MS0 x189 x190 f) 
                                       (MS0 x189 x191 f)) 
                                   (= x190 x191))))) 
                   (or 
                       (and 
                           (forall ((x192 N)) 
                               (=> 
                                   (exists ((x193 N)) 
                                       (and 
                                           (= x193 p) 
                                           (MS0 x193 x192 lt))) 
                                   (MS1 x192 b))) 
                           (forall ((x194 N)) 
                               (=> 
                                   (exists ((x195 N)) 
                                       (and 
                                           (= x195 p) 
                                           (MS0 x195 x194 rt))) 
                                   (MS1 x194 b))) 
                           (not 
                               (= p t)) 
                           (exists ((x196 N)) 
                               (and 
                                   (MS0 p x196 f) 
                                   (MS1 x196 lft)))) 
                       (=> 
                           (and 
                               (forall ((x197 N)) 
                                   (=> 
                                       (exists ((x198 N)) 
                                           (and 
                                               (= x198 p) 
                                               (MS0 x198 x197 lt))) 
                                       (MS1 x197 b))) 
                               (forall ((x199 N)) 
                                   (=> 
                                       (exists ((x200 N)) 
                                           (and 
                                               (= x200 p) 
                                               (MS0 x200 x199 rt))) 
                                       (MS1 x199 b))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x201 N)) 
                                   (MS0 p x201 f)) 
                               (forall ((x202 N) (x203 N) (x204 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x202 x203 f) 
                                           (MS0 x202 x204 f)) 
                                       (= x203 x204))))))))
         :named hyp64))
(assert (! (or 
               (not 
                   (forall ((x205 N)) 
                       (=> 
                           (exists ((x206 N)) 
                               (and 
                                   (= x206 p) 
                                   (MS0 x206 x205 ult))) 
                           (MS1 x205 b)))) 
               (and 
                   (forall ((x207 N)) 
                       (=> 
                           (exists ((x208 N)) 
                               (and 
                                   (= x208 p) 
                                   (MS0 x208 x207 ult))) 
                           (MS1 x207 b))) 
                   (not 
                       (forall ((x209 N)) 
                           (=> 
                               (exists ((x210 N)) 
                                   (and 
                                       (= x210 p) 
                                       (MS0 x210 x209 urt))) 
                               (MS1 x209 b))))) 
               (and 
                   (forall ((x211 N)) 
                       (=> 
                           (exists ((x212 N)) 
                               (and 
                                   (= x212 p) 
                                   (MS0 x212 x211 ult))) 
                           (MS1 x211 b))) 
                   (forall ((x213 N)) 
                       (=> 
                           (exists ((x214 N)) 
                               (and 
                                   (= x214 p) 
                                   (MS0 x214 x213 urt))) 
                           (MS1 x213 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x215 N)) 
                       (and 
                           (MS0 p x215 f) 
                           (MS1 x215 lft)))) 
               (and 
                   (forall ((x216 N)) 
                       (=> 
                           (exists ((x217 N)) 
                               (and 
                                   (= x217 p) 
                                   (MS0 x217 x216 ult))) 
                           (MS1 x216 b))) 
                   (forall ((x218 N)) 
                       (=> 
                           (exists ((x219 N)) 
                               (and 
                                   (= x219 p) 
                                   (MS0 x219 x218 urt))) 
                           (MS1 x218 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x220 N)) 
                       (and 
                           (MS0 p x220 f) 
                           (MS1 x220 rht)))) 
               (and 
                   (forall ((x221 N)) 
                       (=> 
                           (exists ((x222 N)) 
                               (and 
                                   (= x222 p) 
                                   (MS0 x222 x221 ult))) 
                           (MS1 x221 b))) 
                   (forall ((x223 N)) 
                       (=> 
                           (exists ((x224 N)) 
                               (and 
                                   (= x224 p) 
                                   (MS0 x224 x223 urt))) 
                           (MS1 x223 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp65))
(assert (! (or 
               (not 
                   (forall ((x225 N)) 
                       (=> 
                           (exists ((x226 N)) 
                               (and 
                                   (= x226 p) 
                                   (MS0 x226 x225 ult))) 
                           (MS1 x225 b)))) 
               (and 
                   (forall ((x227 N)) 
                       (=> 
                           (exists ((x228 N)) 
                               (and 
                                   (= x228 p) 
                                   (MS0 x228 x227 ult))) 
                           (MS1 x227 b))) 
                   (not 
                       (forall ((x229 N)) 
                           (=> 
                               (exists ((x230 N)) 
                                   (and 
                                       (= x230 p) 
                                       (MS0 x230 x229 urt))) 
                               (MS1 x229 b))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x231 N)) 
                               (=> 
                                   (exists ((x232 N)) 
                                       (and 
                                           (= x232 p) 
                                           (MS0 x232 x231 ult))) 
                                   (MS1 x231 b))) 
                           (forall ((x233 N)) 
                               (=> 
                                   (exists ((x234 N)) 
                                       (and 
                                           (= x234 p) 
                                           (MS0 x234 x233 urt))) 
                                   (MS1 x233 b))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x235 N)) 
                               (MS0 p x235 f)) 
                           (forall ((x236 N) (x237 N) (x238 N)) 
                               (=> 
                                   (and 
                                       (MS0 x236 x237 f) 
                                       (MS0 x236 x238 f)) 
                                   (= x237 x238))))) 
                   (or 
                       (and 
                           (forall ((x239 N)) 
                               (=> 
                                   (exists ((x240 N)) 
                                       (and 
                                           (= x240 p) 
                                           (MS0 x240 x239 ult))) 
                                   (MS1 x239 b))) 
                           (forall ((x241 N)) 
                               (=> 
                                   (exists ((x242 N)) 
                                       (and 
                                           (= x242 p) 
                                           (MS0 x242 x241 urt))) 
                                   (MS1 x241 b))) 
                           (not 
                               (= p t)) 
                           (exists ((x243 N)) 
                               (and 
                                   (MS0 p x243 f) 
                                   (MS1 x243 lft)))) 
                       (=> 
                           (and 
                               (forall ((x244 N)) 
                                   (=> 
                                       (exists ((x245 N)) 
                                           (and 
                                               (= x245 p) 
                                               (MS0 x245 x244 ult))) 
                                       (MS1 x244 b))) 
                               (forall ((x246 N)) 
                                   (=> 
                                       (exists ((x247 N)) 
                                           (and 
                                               (= x247 p) 
                                               (MS0 x247 x246 urt))) 
                                       (MS1 x246 b))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x248 N)) 
                                   (MS0 p x248 f)) 
                               (forall ((x249 N) (x250 N) (x251 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x249 x250 f) 
                                           (MS0 x249 x251 f)) 
                                       (= x250 x251))))))))
         :named hyp66))
(assert (! (or 
               (and 
                   (not 
                       (forall ((x252 N)) 
                           (=> 
                               (exists ((x253 N)) 
                                   (and 
                                       (= x253 p) 
                                       (MS0 x253 x252 g))) 
                               (MS1 x252 b)))) 
                   (exists ((y1 N)) 
                       (and 
                           (MS0 p y1 g) 
                           (not 
                               (MS1 y1 b))))) 
               (and 
                   (forall ((x254 N)) 
                       (=> 
                           (exists ((x255 N)) 
                               (and 
                                   (= x255 p) 
                                   (MS0 x255 x254 g))) 
                           (MS1 x254 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x256 N)) 
                       (=> 
                           (exists ((x257 N)) 
                               (and 
                                   (= x257 p) 
                                   (MS0 x257 x256 g))) 
                           (MS1 x256 b))) 
                   (= p t)))
         :named hyp67))
(assert (! (or 
               (not 
                   (forall ((x258 N)) 
                       (=> 
                           (exists ((x259 N)) 
                               (and 
                                   (= x259 p) 
                                   (MS0 x259 x258 lt))) 
                           (MS1 x258 b)))) 
               (and 
                   (forall ((x260 N)) 
                       (=> 
                           (exists ((x261 N)) 
                               (and 
                                   (= x261 p) 
                                   (MS0 x261 x260 lt))) 
                           (MS1 x260 b))) 
                   (not 
                       (forall ((x262 N)) 
                           (=> 
                               (exists ((x263 N)) 
                                   (and 
                                       (= x263 p) 
                                       (MS0 x263 x262 rt))) 
                               (MS1 x262 b))))) 
               (and 
                   (forall ((x264 N)) 
                       (=> 
                           (exists ((x265 N)) 
                               (and 
                                   (= x265 p) 
                                   (MS0 x265 x264 lt))) 
                           (MS1 x264 b))) 
                   (forall ((x266 N)) 
                       (=> 
                           (exists ((x267 N)) 
                               (and 
                                   (= x267 p) 
                                   (MS0 x267 x266 rt))) 
                           (MS1 x266 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x268 N)) 
                       (=> 
                           (exists ((x269 N)) 
                               (and 
                                   (= x269 p) 
                                   (MS0 x269 x268 lt))) 
                           (MS1 x268 b))) 
                   (forall ((x270 N)) 
                       (=> 
                           (exists ((x271 N)) 
                               (and 
                                   (= x271 p) 
                                   (MS0 x271 x270 rt))) 
                           (MS1 x270 b))) 
                   (= p t)))
         :named hyp68))
(assert (! (or 
               (not 
                   (forall ((x272 N)) 
                       (=> 
                           (exists ((x273 N)) 
                               (and 
                                   (= x273 p) 
                                   (MS0 x273 x272 lt))) 
                           (MS1 x272 b)))) 
               (and 
                   (forall ((x274 N)) 
                       (=> 
                           (exists ((x275 N)) 
                               (and 
                                   (= x275 p) 
                                   (MS0 x275 x274 lt))) 
                           (MS1 x274 b))) 
                   (not 
                       (forall ((x276 N)) 
                           (=> 
                               (exists ((x277 N)) 
                                   (and 
                                       (= x277 p) 
                                       (MS0 x277 x276 rt))) 
                               (MS1 x276 b))))) 
               (and 
                   (forall ((x278 N)) 
                       (=> 
                           (exists ((x279 N)) 
                               (and 
                                   (= x279 p) 
                                   (MS0 x279 x278 lt))) 
                           (MS1 x278 b))) 
                   (forall ((x280 N)) 
                       (=> 
                           (exists ((x281 N)) 
                               (and 
                                   (= x281 p) 
                                   (MS0 x281 x280 rt))) 
                           (MS1 x280 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x282 N)) 
                       (and 
                           (MS0 p x282 f) 
                           (MS1 x282 lft)))) 
               (and 
                   (forall ((x283 N)) 
                       (=> 
                           (exists ((x284 N)) 
                               (and 
                                   (= x284 p) 
                                   (MS0 x284 x283 lt))) 
                           (MS1 x283 b))) 
                   (forall ((x285 N)) 
                       (=> 
                           (exists ((x286 N)) 
                               (and 
                                   (= x286 p) 
                                   (MS0 x286 x285 rt))) 
                           (MS1 x285 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x287 N)) 
                       (and 
                           (MS0 p x287 f) 
                           (MS1 x287 rht)))) 
               (and 
                   (forall ((x288 N)) 
                       (=> 
                           (exists ((x289 N)) 
                               (and 
                                   (= x289 p) 
                                   (MS0 x289 x288 lt))) 
                           (MS1 x288 b))) 
                   (forall ((x290 N)) 
                       (=> 
                           (exists ((x291 N)) 
                               (and 
                                   (= x291 p) 
                                   (MS0 x291 x290 rt))) 
                           (MS1 x290 b))) 
                   (= p t)))
         :named hyp69))
(assert (! (or 
               (not 
                   (forall ((x292 N)) 
                       (=> 
                           (exists ((x293 N)) 
                               (and 
                                   (= x293 p) 
                                   (MS0 x293 x292 ult))) 
                           (MS1 x292 b)))) 
               (and 
                   (forall ((x294 N)) 
                       (=> 
                           (exists ((x295 N)) 
                               (and 
                                   (= x295 p) 
                                   (MS0 x295 x294 ult))) 
                           (MS1 x294 b))) 
                   (not 
                       (forall ((x296 N)) 
                           (=> 
                               (exists ((x297 N)) 
                                   (and 
                                       (= x297 p) 
                                       (MS0 x297 x296 urt))) 
                               (MS1 x296 b))))) 
               (and 
                   (forall ((x298 N)) 
                       (=> 
                           (exists ((x299 N)) 
                               (and 
                                   (= x299 p) 
                                   (MS0 x299 x298 ult))) 
                           (MS1 x298 b))) 
                   (forall ((x300 N)) 
                       (=> 
                           (exists ((x301 N)) 
                               (and 
                                   (= x301 p) 
                                   (MS0 x301 x300 urt))) 
                           (MS1 x300 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x302 N)) 
                       (and 
                           (MS0 p x302 f) 
                           (MS1 x302 lft)))) 
               (and 
                   (forall ((x303 N)) 
                       (=> 
                           (exists ((x304 N)) 
                               (and 
                                   (= x304 p) 
                                   (MS0 x304 x303 ult))) 
                           (MS1 x303 b))) 
                   (forall ((x305 N)) 
                       (=> 
                           (exists ((x306 N)) 
                               (and 
                                   (= x306 p) 
                                   (MS0 x306 x305 urt))) 
                           (MS1 x305 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x307 N)) 
                       (and 
                           (MS0 p x307 f) 
                           (MS1 x307 rht)))) 
               (and 
                   (forall ((x308 N)) 
                       (=> 
                           (exists ((x309 N)) 
                               (and 
                                   (= x309 p) 
                                   (MS0 x309 x308 ult))) 
                           (MS1 x308 b))) 
                   (forall ((x310 N)) 
                       (=> 
                           (exists ((x311 N)) 
                               (and 
                                   (= x311 p) 
                                   (MS0 x311 x310 urt))) 
                           (MS1 x310 b))) 
                   (= p t)))
         :named hyp70))
(assert (! (forall ((x312 N)) 
               (=> 
                   (exists ((x313 N)) 
                       (and 
                           (= x313 p) 
                           (or 
                               (and 
                                   (MS0 x313 x312 ult) 
                                   (not 
                                       (exists ((x314 N)) 
                                           (and 
                                               (= x313 t) 
                                               (= x314 nil) 
                                               (MS1 x313 lft))))) 
                               (and 
                                   (= x313 t) 
                                   (= x312 nil) 
                                   (MS1 x313 lft))))) 
                   (MS1 x312 b)))
         :named hyp71))
(assert (! (forall ((x315 N) (x316 N) (x317 N)) 
               (=> 
                   (and 
                       (or 
                           (and 
                               (MS0 x315 x316 urt) 
                               (not 
                                   (exists ((x318 N)) 
                                       (and 
                                           (= x315 t) 
                                           (= x318 nil) 
                                           (MS1 x315 rht))))) 
                           (and 
                               (= x315 t) 
                               (= x316 nil) 
                               (MS1 x315 rht))) 
                       (or 
                           (and 
                               (MS0 x315 x317 urt) 
                               (not 
                                   (exists ((x319 N)) 
                                       (and 
                                           (= x315 t) 
                                           (= x319 nil) 
                                           (MS1 x315 rht))))) 
                           (and 
                               (= x315 t) 
                               (= x317 nil) 
                               (MS1 x315 rht)))) 
                   (= x316 x317)))
         :named hyp72))
(assert (! (not 
               (forall ((x320 N)) 
                   (=> 
                       (exists ((x321 N)) 
                           (and 
                               (= x321 p) 
                               (or 
                                   (and 
                                       (MS0 x321 x320 urt) 
                                       (not 
                                           (exists ((x322 N)) 
                                               (and 
                                                   (= x321 t) 
                                                   (= x322 nil) 
                                                   (MS1 x321 rht))))) 
                                   (and 
                                       (= x321 t) 
                                       (= x320 nil) 
                                       (MS1 x321 rht))))) 
                       (MS1 x320 b))))
         :named hyp73))
(assert (! (and 
               (= p t) 
               (MS1 p rht))
         :named hyp74))
(assert (! (not 
               (and 
                   (= p t) 
                   (MS0 p nil urt) 
                   (MS1 p rht)))
         :named goal))
(check-sat)
(exit)

