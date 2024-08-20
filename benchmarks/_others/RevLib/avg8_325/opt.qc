# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/RevLib/avg8_325/circuit.qc):
#   Qubits: 320
#   H: 992
#   T: 3472
#   cnot: 4237
#   Depth: 4471
#   T depth: 1503
# Result (18.756ms):
#   Qubits: 320
#   H: 992
#   T: 3472
#   cnot: 4237
#   Depth: 4471
#   T depth: 1503
.v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94 q95 q96 q97 q98 q99 q100 q101 q102 q103 q104 q105 q106 q107 q108 q109 q110 q111 q112 q113 q114 q115 q116 q117 q118 q119 q120 q121 q122 q123 q124 q125 q126 q127 q128 q129 q130 q131 q132 q133 q134 q135 q136 q137 q138 q139 q140 q141 q142 q143 q144 q145 q146 q147 q148 q149 q150 q151 q152 q153 q154 q155 q156 q157 q158 q159 q160 q161 q162 q163 q164 q165 q166 q167 q168 q169 q170 q171 q172 q173 q174 q175 q176 q177 q178 q179 q180 q181 q182 q183 q184 q185 q186 q187 q188 q189 q190 q191 q192 q193 q194 q195 q196 q197 q198 q199 q200 q201 q202 q203 q204 q205 q206 q207 q208 q209 q210 q211 q212 q213 q214 q215 q216 q217 q218 q219 q220 q221 q222 q223 q224 q225 q226 q227 q228 q229 q230 q231 q232 q233 q234 q235 q236 q237 q238 q239 q240 q241 q242 q243 q244 q245 q246 q247 q248 q249 q250 q251 q252 q253 q254 q255 q256 q257 q258 q259 q260 q261 q262 q263 q264 q265 q266 q267 q268 q269 q270 q271 q272 q273 q274 q275 q276 q277 q278 q279 q280 q281 q282 q283 q284 q285 q286 q287 q288 q289 q290 q291 q292 q293 q294 q295 q296 q297 q298 q299 q300 q301 q302 q303 q304 q305 q306 q307 q308 q309 q310 q311 q312 q313 q314 q315 q316 q317 q318 q319
.i q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94 q95 q96 q97 q98 q99 q100 q101 q102 q103 q104 q105 q106 q107 q108 q109 q110 q111 q112 q113 q114 q115 q116 q117 q118 q119 q120 q121 q122 q123 q124 q125 q126 q127 q128 q129 q130 q131 q132 q133 q134 q135 q136 q137 q138 q139 q140 q141 q142 q143 q144 q145 q146 q147 q148 q149 q150 q151 q152 q153 q154 q155 q156 q157 q158 q159 q160 q161 q162 q163 q164 q165 q166 q167 q168 q169 q170 q171 q172 q173 q174 q175 q176 q177 q178 q179 q180 q181 q182 q183 q184 q185 q186 q187 q188 q189 q190 q191 q192 q193 q194 q195 q196 q197 q198 q199 q200 q201 q202 q203 q204 q205 q206 q207 q208 q209 q210 q211 q212 q213 q214 q215 q216 q217 q218 q219 q220 q221 q222 q223 q224 q225 q226 q227 q228 q229 q230 q231 q232 q233 q234 q235 q236 q237 q238 q239 q240 q241 q242 q243 q244 q245 q246 q247 q248 q249 q250 q251 q252 q253 q254 q255 q256 q257 q258 q259 q260 q261 q262 q263 q264 q265 q266 q267 q268 q269 q270 q271 q272 q273 q274 q275 q276 q277 q278 q279 q280 q281 q282 q283 q284 q285 q286 q287 q288 q289 q290 q291 q292 q293 q294 q295 q296 q297 q298 q299 q300 q301 q302 q303 q304 q305 q306 q307 q308 q309 q310 q311 q312 q313 q314 q315 q316 q317 q318 q319
.o q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40 q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94 q95 q96 q97 q98 q99 q100 q101 q102 q103 q104 q105 q106 q107 q108 q109 q110 q111 q112 q113 q114 q115 q116 q117 q118 q119 q120 q121 q122 q123 q124 q125 q126 q127 q128 q129 q130 q131 q132 q133 q134 q135 q136 q137 q138 q139 q140 q141 q142 q143 q144 q145 q146 q147 q148 q149 q150 q151 q152 q153 q154 q155 q156 q157 q158 q159 q160 q161 q162 q163 q164 q165 q166 q167 q168 q169 q170 q171 q172 q173 q174 q175 q176 q177 q178 q179 q180 q181 q182 q183 q184 q185 q186 q187 q188 q189 q190 q191 q192 q193 q194 q195 q196 q197 q198 q199 q200 q201 q202 q203 q204 q205 q206 q207 q208 q209 q210 q211 q212 q213 q214 q215 q216 q217 q218 q219 q220 q221 q222 q223 q224 q225 q226 q227 q228 q229 q230 q231 q232 q233 q234 q235 q236 q237 q238 q239 q240 q241 q242 q243 q244 q245 q246 q247 q248 q249 q250 q251 q252 q253 q254 q255 q256 q257 q258 q259 q260 q261 q262 q263 q264 q265 q266 q267 q268 q269 q270 q271 q272 q273 q274 q275 q276 q277 q278 q279 q280 q281 q282 q283 q284 q285 q286 q287 q288 q289 q290 q291 q292 q293 q294 q295 q296 q297 q298 q299 q300 q301 q302 q303 q304 q305 q306 q307 q308 q309 q310 q311 q312 q313 q314 q315 q316 q317 q318 q319
BEGIN 
tof q65 q33
tof q66 q34
tof q67 q35
tof q68 q36
tof q69 q37
tof q70 q38
tof q71 q39
tof q72 q40
tof q73 q41
tof q74 q42
tof q75 q43
tof q76 q44
tof q77 q45
tof q78 q46
tof q79 q47
tof q80 q48
tof q81 q49
tof q82 q50
tof q83 q51
tof q84 q52
tof q85 q53
tof q86 q54
tof q87 q55
tof q88 q56
tof q89 q57
tof q90 q58
tof q91 q59
tof q92 q60
tof q93 q61
tof q94 q62
tof q95 q63
tof q94 q95
tof q93 q94
tof q92 q93
tof q91 q92
tof q90 q91
tof q89 q90
tof q88 q89
tof q87 q88
tof q86 q87
tof q85 q86
tof q84 q85
tof q83 q84
tof q82 q83
tof q81 q82
tof q80 q81
tof q79 q80
tof q78 q79
tof q77 q78
tof q76 q77
tof q75 q76
tof q74 q75
tof q73 q74
tof q72 q73
tof q71 q72
tof q70 q71
tof q69 q70
tof q68 q69
tof q67 q68
tof q66 q67
tof q65 q66
tof q32 q64 q65
tof q33 q65 q66
tof q34 q66 q67
tof q35 q67 q68
tof q36 q68 q69
tof q37 q69 q70
tof q38 q70 q71
tof q39 q71 q72
tof q40 q72 q73
tof q41 q73 q74
tof q42 q74 q75
tof q43 q75 q76
tof q44 q76 q77
tof q45 q77 q78
tof q46 q78 q79
tof q47 q79 q80
tof q48 q80 q81
tof q49 q81 q82
tof q50 q82 q83
tof q51 q83 q84
tof q52 q84 q85
tof q53 q85 q86
tof q54 q86 q87
tof q55 q87 q88
tof q56 q88 q89
tof q57 q89 q90
tof q58 q90 q91
tof q59 q91 q92
tof q60 q92 q93
tof q61 q93 q94
tof q62 q94 q95
tof q95 q63
tof q62 q94 q95
tof q94 q62
tof q61 q93 q94
tof q93 q61
tof q60 q92 q93
tof q92 q60
tof q59 q91 q92
tof q91 q59
tof q58 q90 q91
tof q90 q58
tof q57 q89 q90
tof q89 q57
tof q56 q88 q89
tof q88 q56
tof q55 q87 q88
tof q87 q55
tof q54 q86 q87
tof q86 q54
tof q53 q85 q86
tof q85 q53
tof q52 q84 q85
tof q84 q52
tof q51 q83 q84
tof q83 q51
tof q50 q82 q83
tof q82 q50
tof q49 q81 q82
tof q81 q49
tof q48 q80 q81
tof q80 q48
tof q47 q79 q80
tof q79 q47
tof q46 q78 q79
tof q78 q46
tof q45 q77 q78
tof q77 q45
tof q44 q76 q77
tof q76 q44
tof q43 q75 q76
tof q75 q43
tof q42 q74 q75
tof q74 q42
tof q41 q73 q74
tof q73 q41
tof q40 q72 q73
tof q72 q40
tof q39 q71 q72
tof q71 q39
tof q38 q70 q71
tof q70 q38
tof q37 q69 q70
tof q69 q37
tof q36 q68 q69
tof q68 q36
tof q35 q67 q68
tof q67 q35
tof q34 q66 q67
tof q66 q34
tof q33 q65 q66
tof q65 q33
tof q32 q64 q65
tof q65 q66
tof q66 q67
tof q67 q68
tof q68 q69
tof q69 q70
tof q70 q71
tof q71 q72
tof q72 q73
tof q73 q74
tof q74 q75
tof q75 q76
tof q76 q77
tof q77 q78
tof q78 q79
tof q79 q80
tof q80 q81
tof q81 q82
tof q82 q83
tof q83 q84
tof q84 q85
tof q85 q86
tof q86 q87
tof q87 q88
tof q88 q89
tof q89 q90
tof q90 q91
tof q91 q92
tof q92 q93
tof q93 q94
tof q94 q95
tof q64 q32
tof q65 q33
tof q66 q34
tof q67 q35
tof q68 q36
tof q69 q37
tof q70 q38
tof q71 q39
tof q72 q40
tof q73 q41
tof q74 q42
tof q75 q43
tof q76 q44
tof q77 q45
tof q78 q46
tof q79 q47
tof q80 q48
tof q81 q49
tof q82 q50
tof q83 q51
tof q84 q52
tof q85 q53
tof q86 q54
tof q87 q55
tof q88 q56
tof q89 q57
tof q90 q58
tof q91 q59
tof q92 q60
tof q93 q61
tof q94 q62
tof q95 q63
tof q97 q33
tof q98 q34
tof q99 q35
tof q100 q36
tof q101 q37
tof q102 q38
tof q103 q39
tof q104 q40
tof q105 q41
tof q106 q42
tof q107 q43
tof q108 q44
tof q109 q45
tof q110 q46
tof q111 q47
tof q112 q48
tof q113 q49
tof q114 q50
tof q115 q51
tof q116 q52
tof q117 q53
tof q118 q54
tof q119 q55
tof q120 q56
tof q121 q57
tof q122 q58
tof q123 q59
tof q124 q60
tof q125 q61
tof q126 q62
tof q127 q63
tof q126 q127
tof q125 q126
tof q124 q125
tof q123 q124
tof q122 q123
tof q121 q122
tof q120 q121
tof q119 q120
tof q118 q119
tof q117 q118
tof q116 q117
tof q115 q116
tof q114 q115
tof q113 q114
tof q112 q113
tof q111 q112
tof q110 q111
tof q109 q110
tof q108 q109
tof q107 q108
tof q106 q107
tof q105 q106
tof q104 q105
tof q103 q104
tof q102 q103
tof q101 q102
tof q100 q101
tof q99 q100
tof q98 q99
tof q97 q98
tof q32 q96 q97
tof q33 q97 q98
tof q34 q98 q99
tof q35 q99 q100
tof q36 q100 q101
tof q37 q101 q102
tof q38 q102 q103
tof q39 q103 q104
tof q40 q104 q105
tof q41 q105 q106
tof q42 q106 q107
tof q43 q107 q108
tof q44 q108 q109
tof q45 q109 q110
tof q46 q110 q111
tof q47 q111 q112
tof q48 q112 q113
tof q49 q113 q114
tof q50 q114 q115
tof q51 q115 q116
tof q52 q116 q117
tof q53 q117 q118
tof q54 q118 q119
tof q55 q119 q120
tof q56 q120 q121
tof q57 q121 q122
tof q58 q122 q123
tof q59 q123 q124
tof q60 q124 q125
tof q61 q125 q126
tof q62 q126 q127
tof q127 q63
tof q62 q126 q127
tof q126 q62
tof q61 q125 q126
tof q125 q61
tof q60 q124 q125
tof q124 q60
tof q59 q123 q124
tof q123 q59
tof q58 q122 q123
tof q122 q58
tof q57 q121 q122
tof q121 q57
tof q56 q120 q121
tof q120 q56
tof q55 q119 q120
tof q119 q55
tof q54 q118 q119
tof q118 q54
tof q53 q117 q118
tof q117 q53
tof q52 q116 q117
tof q116 q52
tof q51 q115 q116
tof q115 q51
tof q50 q114 q115
tof q114 q50
tof q49 q113 q114
tof q113 q49
tof q48 q112 q113
tof q112 q48
tof q47 q111 q112
tof q111 q47
tof q46 q110 q111
tof q110 q46
tof q45 q109 q110
tof q109 q45
tof q44 q108 q109
tof q108 q44
tof q43 q107 q108
tof q107 q43
tof q42 q106 q107
tof q106 q42
tof q41 q105 q106
tof q105 q41
tof q40 q104 q105
tof q104 q40
tof q39 q103 q104
tof q103 q39
tof q38 q102 q103
tof q102 q38
tof q37 q101 q102
tof q101 q37
tof q36 q100 q101
tof q100 q36
tof q35 q99 q100
tof q99 q35
tof q34 q98 q99
tof q98 q34
tof q33 q97 q98
tof q97 q33
tof q32 q96 q97
tof q97 q98
tof q98 q99
tof q99 q100
tof q100 q101
tof q101 q102
tof q102 q103
tof q103 q104
tof q104 q105
tof q105 q106
tof q106 q107
tof q107 q108
tof q108 q109
tof q109 q110
tof q110 q111
tof q111 q112
tof q112 q113
tof q113 q114
tof q114 q115
tof q115 q116
tof q116 q117
tof q117 q118
tof q118 q119
tof q119 q120
tof q120 q121
tof q121 q122
tof q122 q123
tof q123 q124
tof q124 q125
tof q125 q126
tof q126 q127
tof q96 q32
tof q97 q33
tof q98 q34
tof q99 q35
tof q100 q36
tof q101 q37
tof q102 q38
tof q103 q39
tof q104 q40
tof q105 q41
tof q106 q42
tof q107 q43
tof q108 q44
tof q109 q45
tof q110 q46
tof q111 q47
tof q112 q48
tof q113 q49
tof q114 q50
tof q115 q51
tof q116 q52
tof q117 q53
tof q118 q54
tof q119 q55
tof q120 q56
tof q121 q57
tof q122 q58
tof q123 q59
tof q124 q60
tof q125 q61
tof q126 q62
tof q127 q63
tof q129 q33
tof q130 q34
tof q131 q35
tof q132 q36
tof q133 q37
tof q134 q38
tof q135 q39
tof q136 q40
tof q137 q41
tof q138 q42
tof q139 q43
tof q140 q44
tof q141 q45
tof q142 q46
tof q143 q47
tof q144 q48
tof q145 q49
tof q146 q50
tof q147 q51
tof q148 q52
tof q149 q53
tof q150 q54
tof q151 q55
tof q152 q56
tof q153 q57
tof q154 q58
tof q155 q59
tof q156 q60
tof q157 q61
tof q158 q62
tof q159 q63
tof q158 q159
tof q157 q158
tof q156 q157
tof q155 q156
tof q154 q155
tof q153 q154
tof q152 q153
tof q151 q152
tof q150 q151
tof q149 q150
tof q148 q149
tof q147 q148
tof q146 q147
tof q145 q146
tof q144 q145
tof q143 q144
tof q142 q143
tof q141 q142
tof q140 q141
tof q139 q140
tof q138 q139
tof q137 q138
tof q136 q137
tof q135 q136
tof q134 q135
tof q133 q134
tof q132 q133
tof q131 q132
tof q130 q131
tof q129 q130
tof q32 q128 q129
tof q33 q129 q130
tof q34 q130 q131
tof q35 q131 q132
tof q36 q132 q133
tof q37 q133 q134
tof q38 q134 q135
tof q39 q135 q136
tof q40 q136 q137
tof q41 q137 q138
tof q42 q138 q139
tof q43 q139 q140
tof q44 q140 q141
tof q45 q141 q142
tof q46 q142 q143
tof q47 q143 q144
tof q48 q144 q145
tof q49 q145 q146
tof q50 q146 q147
tof q51 q147 q148
tof q52 q148 q149
tof q53 q149 q150
tof q54 q150 q151
tof q55 q151 q152
tof q56 q152 q153
tof q57 q153 q154
tof q58 q154 q155
tof q59 q155 q156
tof q60 q156 q157
tof q61 q157 q158
tof q62 q158 q159
tof q159 q63
tof q62 q158 q159
tof q158 q62
tof q61 q157 q158
tof q157 q61
tof q60 q156 q157
tof q156 q60
tof q59 q155 q156
tof q155 q59
tof q58 q154 q155
tof q154 q58
tof q57 q153 q154
tof q153 q57
tof q56 q152 q153
tof q152 q56
tof q55 q151 q152
tof q151 q55
tof q54 q150 q151
tof q150 q54
tof q53 q149 q150
tof q149 q53
tof q52 q148 q149
tof q148 q52
tof q51 q147 q148
tof q147 q51
tof q50 q146 q147
tof q146 q50
tof q49 q145 q146
tof q145 q49
tof q48 q144 q145
tof q144 q48
tof q47 q143 q144
tof q143 q47
tof q46 q142 q143
tof q142 q46
tof q45 q141 q142
tof q141 q45
tof q44 q140 q141
tof q140 q44
tof q43 q139 q140
tof q139 q43
tof q42 q138 q139
tof q138 q42
tof q41 q137 q138
tof q137 q41
tof q40 q136 q137
tof q136 q40
tof q39 q135 q136
tof q135 q39
tof q38 q134 q135
tof q134 q38
tof q37 q133 q134
tof q133 q37
tof q36 q132 q133
tof q132 q36
tof q35 q131 q132
tof q131 q35
tof q34 q130 q131
tof q130 q34
tof q33 q129 q130
tof q129 q33
tof q32 q128 q129
tof q129 q130
tof q130 q131
tof q131 q132
tof q132 q133
tof q133 q134
tof q134 q135
tof q135 q136
tof q136 q137
tof q137 q138
tof q138 q139
tof q139 q140
tof q140 q141
tof q141 q142
tof q142 q143
tof q143 q144
tof q144 q145
tof q145 q146
tof q146 q147
tof q147 q148
tof q148 q149
tof q149 q150
tof q150 q151
tof q151 q152
tof q152 q153
tof q153 q154
tof q154 q155
tof q155 q156
tof q156 q157
tof q157 q158
tof q158 q159
tof q128 q32
tof q129 q33
tof q130 q34
tof q131 q35
tof q132 q36
tof q133 q37
tof q134 q38
tof q135 q39
tof q136 q40
tof q137 q41
tof q138 q42
tof q139 q43
tof q140 q44
tof q141 q45
tof q142 q46
tof q143 q47
tof q144 q48
tof q145 q49
tof q146 q50
tof q147 q51
tof q148 q52
tof q149 q53
tof q150 q54
tof q151 q55
tof q152 q56
tof q153 q57
tof q154 q58
tof q155 q59
tof q156 q60
tof q157 q61
tof q158 q62
tof q159 q63
tof q161 q33
tof q162 q34
tof q163 q35
tof q164 q36
tof q165 q37
tof q166 q38
tof q167 q39
tof q168 q40
tof q169 q41
tof q170 q42
tof q171 q43
tof q172 q44
tof q173 q45
tof q174 q46
tof q175 q47
tof q176 q48
tof q177 q49
tof q178 q50
tof q179 q51
tof q180 q52
tof q181 q53
tof q182 q54
tof q183 q55
tof q184 q56
tof q185 q57
tof q186 q58
tof q187 q59
tof q188 q60
tof q189 q61
tof q190 q62
tof q191 q63
tof q190 q191
tof q189 q190
tof q188 q189
tof q187 q188
tof q186 q187
tof q185 q186
tof q184 q185
tof q183 q184
tof q182 q183
tof q181 q182
tof q180 q181
tof q179 q180
tof q178 q179
tof q177 q178
tof q176 q177
tof q175 q176
tof q174 q175
tof q173 q174
tof q172 q173
tof q171 q172
tof q170 q171
tof q169 q170
tof q168 q169
tof q167 q168
tof q166 q167
tof q165 q166
tof q164 q165
tof q163 q164
tof q162 q163
tof q161 q162
tof q32 q160 q161
tof q33 q161 q162
tof q34 q162 q163
tof q35 q163 q164
tof q36 q164 q165
tof q37 q165 q166
tof q38 q166 q167
tof q39 q167 q168
tof q40 q168 q169
tof q41 q169 q170
tof q42 q170 q171
tof q43 q171 q172
tof q44 q172 q173
tof q45 q173 q174
tof q46 q174 q175
tof q47 q175 q176
tof q48 q176 q177
tof q49 q177 q178
tof q50 q178 q179
tof q51 q179 q180
tof q52 q180 q181
tof q53 q181 q182
tof q54 q182 q183
tof q55 q183 q184
tof q56 q184 q185
tof q57 q185 q186
tof q58 q186 q187
tof q59 q187 q188
tof q60 q188 q189
tof q61 q189 q190
tof q62 q190 q191
tof q191 q63
tof q62 q190 q191
tof q190 q62
tof q61 q189 q190
tof q189 q61
tof q60 q188 q189
tof q188 q60
tof q59 q187 q188
tof q187 q59
tof q58 q186 q187
tof q186 q58
tof q57 q185 q186
tof q185 q57
tof q56 q184 q185
tof q184 q56
tof q55 q183 q184
tof q183 q55
tof q54 q182 q183
tof q182 q54
tof q53 q181 q182
tof q181 q53
tof q52 q180 q181
tof q180 q52
tof q51 q179 q180
tof q179 q51
tof q50 q178 q179
tof q178 q50
tof q49 q177 q178
tof q177 q49
tof q48 q176 q177
tof q176 q48
tof q47 q175 q176
tof q175 q47
tof q46 q174 q175
tof q174 q46
tof q45 q173 q174
tof q173 q45
tof q44 q172 q173
tof q172 q44
tof q43 q171 q172
tof q171 q43
tof q42 q170 q171
tof q170 q42
tof q41 q169 q170
tof q169 q41
tof q40 q168 q169
tof q168 q40
tof q39 q167 q168
tof q167 q39
tof q38 q166 q167
tof q166 q38
tof q37 q165 q166
tof q165 q37
tof q36 q164 q165
tof q164 q36
tof q35 q163 q164
tof q163 q35
tof q34 q162 q163
tof q162 q34
tof q33 q161 q162
tof q161 q33
tof q32 q160 q161
tof q161 q162
tof q162 q163
tof q163 q164
tof q164 q165
tof q165 q166
tof q166 q167
tof q167 q168
tof q168 q169
tof q169 q170
tof q170 q171
tof q171 q172
tof q172 q173
tof q173 q174
tof q174 q175
tof q175 q176
tof q176 q177
tof q177 q178
tof q178 q179
tof q179 q180
tof q180 q181
tof q181 q182
tof q182 q183
tof q183 q184
tof q184 q185
tof q185 q186
tof q186 q187
tof q187 q188
tof q188 q189
tof q189 q190
tof q190 q191
tof q160 q32
tof q161 q33
tof q162 q34
tof q163 q35
tof q164 q36
tof q165 q37
tof q166 q38
tof q167 q39
tof q168 q40
tof q169 q41
tof q170 q42
tof q171 q43
tof q172 q44
tof q173 q45
tof q174 q46
tof q175 q47
tof q176 q48
tof q177 q49
tof q178 q50
tof q179 q51
tof q180 q52
tof q181 q53
tof q182 q54
tof q183 q55
tof q184 q56
tof q185 q57
tof q186 q58
tof q187 q59
tof q188 q60
tof q189 q61
tof q190 q62
tof q191 q63
tof q193 q33
tof q194 q34
tof q195 q35
tof q196 q36
tof q197 q37
tof q198 q38
tof q199 q39
tof q200 q40
tof q201 q41
tof q202 q42
tof q203 q43
tof q204 q44
tof q205 q45
tof q206 q46
tof q207 q47
tof q208 q48
tof q209 q49
tof q210 q50
tof q211 q51
tof q212 q52
tof q213 q53
tof q214 q54
tof q215 q55
tof q216 q56
tof q217 q57
tof q218 q58
tof q219 q59
tof q220 q60
tof q221 q61
tof q222 q62
tof q223 q63
tof q222 q223
tof q221 q222
tof q220 q221
tof q219 q220
tof q218 q219
tof q217 q218
tof q216 q217
tof q215 q216
tof q214 q215
tof q213 q214
tof q212 q213
tof q211 q212
tof q210 q211
tof q209 q210
tof q208 q209
tof q207 q208
tof q206 q207
tof q205 q206
tof q204 q205
tof q203 q204
tof q202 q203
tof q201 q202
tof q200 q201
tof q199 q200
tof q198 q199
tof q197 q198
tof q196 q197
tof q195 q196
tof q194 q195
tof q193 q194
tof q32 q192 q193
tof q33 q193 q194
tof q34 q194 q195
tof q35 q195 q196
tof q36 q196 q197
tof q37 q197 q198
tof q38 q198 q199
tof q39 q199 q200
tof q40 q200 q201
tof q41 q201 q202
tof q42 q202 q203
tof q43 q203 q204
tof q44 q204 q205
tof q45 q205 q206
tof q46 q206 q207
tof q47 q207 q208
tof q48 q208 q209
tof q49 q209 q210
tof q50 q210 q211
tof q51 q211 q212
tof q52 q212 q213
tof q53 q213 q214
tof q54 q214 q215
tof q55 q215 q216
tof q56 q216 q217
tof q57 q217 q218
tof q58 q218 q219
tof q59 q219 q220
tof q60 q220 q221
tof q61 q221 q222
tof q62 q222 q223
tof q223 q63
tof q62 q222 q223
tof q222 q62
tof q61 q221 q222
tof q221 q61
tof q60 q220 q221
tof q220 q60
tof q59 q219 q220
tof q219 q59
tof q58 q218 q219
tof q218 q58
tof q57 q217 q218
tof q217 q57
tof q56 q216 q217
tof q216 q56
tof q55 q215 q216
tof q215 q55
tof q54 q214 q215
tof q214 q54
tof q53 q213 q214
tof q213 q53
tof q52 q212 q213
tof q212 q52
tof q51 q211 q212
tof q211 q51
tof q50 q210 q211
tof q210 q50
tof q49 q209 q210
tof q209 q49
tof q48 q208 q209
tof q208 q48
tof q47 q207 q208
tof q207 q47
tof q46 q206 q207
tof q206 q46
tof q45 q205 q206
tof q205 q45
tof q44 q204 q205
tof q204 q44
tof q43 q203 q204
tof q203 q43
tof q42 q202 q203
tof q202 q42
tof q41 q201 q202
tof q201 q41
tof q40 q200 q201
tof q200 q40
tof q39 q199 q200
tof q199 q39
tof q38 q198 q199
tof q198 q38
tof q37 q197 q198
tof q197 q37
tof q36 q196 q197
tof q196 q36
tof q35 q195 q196
tof q195 q35
tof q34 q194 q195
tof q194 q34
tof q33 q193 q194
tof q193 q33
tof q32 q192 q193
tof q193 q194
tof q194 q195
tof q195 q196
tof q196 q197
tof q197 q198
tof q198 q199
tof q199 q200
tof q200 q201
tof q201 q202
tof q202 q203
tof q203 q204
tof q204 q205
tof q205 q206
tof q206 q207
tof q207 q208
tof q208 q209
tof q209 q210
tof q210 q211
tof q211 q212
tof q212 q213
tof q213 q214
tof q214 q215
tof q215 q216
tof q216 q217
tof q217 q218
tof q218 q219
tof q219 q220
tof q220 q221
tof q221 q222
tof q222 q223
tof q192 q32
tof q193 q33
tof q194 q34
tof q195 q35
tof q196 q36
tof q197 q37
tof q198 q38
tof q199 q39
tof q200 q40
tof q201 q41
tof q202 q42
tof q203 q43
tof q204 q44
tof q205 q45
tof q206 q46
tof q207 q47
tof q208 q48
tof q209 q49
tof q210 q50
tof q211 q51
tof q212 q52
tof q213 q53
tof q214 q54
tof q215 q55
tof q216 q56
tof q217 q57
tof q218 q58
tof q219 q59
tof q220 q60
tof q221 q61
tof q222 q62
tof q223 q63
tof q225 q33
tof q226 q34
tof q227 q35
tof q228 q36
tof q229 q37
tof q230 q38
tof q231 q39
tof q232 q40
tof q233 q41
tof q234 q42
tof q235 q43
tof q236 q44
tof q237 q45
tof q238 q46
tof q239 q47
tof q240 q48
tof q241 q49
tof q242 q50
tof q243 q51
tof q244 q52
tof q245 q53
tof q246 q54
tof q247 q55
tof q248 q56
tof q249 q57
tof q250 q58
tof q251 q59
tof q252 q60
tof q253 q61
tof q254 q62
tof q255 q63
tof q254 q255
tof q253 q254
tof q252 q253
tof q251 q252
tof q250 q251
tof q249 q250
tof q248 q249
tof q247 q248
tof q246 q247
tof q245 q246
tof q244 q245
tof q243 q244
tof q242 q243
tof q241 q242
tof q240 q241
tof q239 q240
tof q238 q239
tof q237 q238
tof q236 q237
tof q235 q236
tof q234 q235
tof q233 q234
tof q232 q233
tof q231 q232
tof q230 q231
tof q229 q230
tof q228 q229
tof q227 q228
tof q226 q227
tof q225 q226
tof q32 q224 q225
tof q33 q225 q226
tof q34 q226 q227
tof q35 q227 q228
tof q36 q228 q229
tof q37 q229 q230
tof q38 q230 q231
tof q39 q231 q232
tof q40 q232 q233
tof q41 q233 q234
tof q42 q234 q235
tof q43 q235 q236
tof q44 q236 q237
tof q45 q237 q238
tof q46 q238 q239
tof q47 q239 q240
tof q48 q240 q241
tof q49 q241 q242
tof q50 q242 q243
tof q51 q243 q244
tof q52 q244 q245
tof q53 q245 q246
tof q54 q246 q247
tof q55 q247 q248
tof q56 q248 q249
tof q57 q249 q250
tof q58 q250 q251
tof q59 q251 q252
tof q60 q252 q253
tof q61 q253 q254
tof q62 q254 q255
tof q255 q63
tof q62 q254 q255
tof q254 q62
tof q61 q253 q254
tof q253 q61
tof q60 q252 q253
tof q252 q60
tof q59 q251 q252
tof q251 q59
tof q58 q250 q251
tof q250 q58
tof q57 q249 q250
tof q249 q57
tof q56 q248 q249
tof q248 q56
tof q55 q247 q248
tof q247 q55
tof q54 q246 q247
tof q246 q54
tof q53 q245 q246
tof q245 q53
tof q52 q244 q245
tof q244 q52
tof q51 q243 q244
tof q243 q51
tof q50 q242 q243
tof q242 q50
tof q49 q241 q242
tof q241 q49
tof q48 q240 q241
tof q240 q48
tof q47 q239 q240
tof q239 q47
tof q46 q238 q239
tof q238 q46
tof q45 q237 q238
tof q237 q45
tof q44 q236 q237
tof q236 q44
tof q43 q235 q236
tof q235 q43
tof q42 q234 q235
tof q234 q42
tof q41 q233 q234
tof q233 q41
tof q40 q232 q233
tof q232 q40
tof q39 q231 q232
tof q231 q39
tof q38 q230 q231
tof q230 q38
tof q37 q229 q230
tof q229 q37
tof q36 q228 q229
tof q228 q36
tof q35 q227 q228
tof q227 q35
tof q34 q226 q227
tof q226 q34
tof q33 q225 q226
tof q225 q33
tof q32 q224 q225
tof q225 q226
tof q226 q227
tof q227 q228
tof q228 q229
tof q229 q230
tof q230 q231
tof q231 q232
tof q232 q233
tof q233 q234
tof q234 q235
tof q235 q236
tof q236 q237
tof q237 q238
tof q238 q239
tof q239 q240
tof q240 q241
tof q241 q242
tof q242 q243
tof q243 q244
tof q244 q245
tof q245 q246
tof q246 q247
tof q247 q248
tof q248 q249
tof q249 q250
tof q250 q251
tof q251 q252
tof q252 q253
tof q253 q254
tof q254 q255
tof q224 q32
tof q225 q33
tof q226 q34
tof q227 q35
tof q228 q36
tof q229 q37
tof q230 q38
tof q231 q39
tof q232 q40
tof q233 q41
tof q234 q42
tof q235 q43
tof q236 q44
tof q237 q45
tof q238 q46
tof q239 q47
tof q240 q48
tof q241 q49
tof q242 q50
tof q243 q51
tof q244 q52
tof q245 q53
tof q246 q54
tof q247 q55
tof q248 q56
tof q249 q57
tof q250 q58
tof q251 q59
tof q252 q60
tof q253 q61
tof q254 q62
tof q255 q63
tof q257 q33
tof q258 q34
tof q259 q35
tof q260 q36
tof q261 q37
tof q262 q38
tof q263 q39
tof q264 q40
tof q265 q41
tof q266 q42
tof q267 q43
tof q268 q44
tof q269 q45
tof q270 q46
tof q271 q47
tof q272 q48
tof q273 q49
tof q274 q50
tof q275 q51
tof q276 q52
tof q277 q53
tof q278 q54
tof q279 q55
tof q280 q56
tof q281 q57
tof q282 q58
tof q283 q59
tof q284 q60
tof q285 q61
tof q286 q62
tof q287 q63
tof q286 q287
tof q285 q286
tof q284 q285
tof q283 q284
tof q282 q283
tof q281 q282
tof q280 q281
tof q279 q280
tof q278 q279
tof q277 q278
tof q276 q277
tof q275 q276
tof q274 q275
tof q273 q274
tof q272 q273
tof q271 q272
tof q270 q271
tof q269 q270
tof q268 q269
tof q267 q268
tof q266 q267
tof q265 q266
tof q264 q265
tof q263 q264
tof q262 q263
tof q261 q262
tof q260 q261
tof q259 q260
tof q258 q259
tof q257 q258
tof q32 q256 q257
tof q33 q257 q258
tof q34 q258 q259
tof q35 q259 q260
tof q36 q260 q261
tof q37 q261 q262
tof q38 q262 q263
tof q39 q263 q264
tof q40 q264 q265
tof q41 q265 q266
tof q42 q266 q267
tof q43 q267 q268
tof q44 q268 q269
tof q45 q269 q270
tof q46 q270 q271
tof q47 q271 q272
tof q48 q272 q273
tof q49 q273 q274
tof q50 q274 q275
tof q51 q275 q276
tof q52 q276 q277
tof q53 q277 q278
tof q54 q278 q279
tof q55 q279 q280
tof q56 q280 q281
tof q57 q281 q282
tof q58 q282 q283
tof q59 q283 q284
tof q60 q284 q285
tof q61 q285 q286
tof q62 q286 q287
tof q287 q63
tof q62 q286 q287
tof q286 q62
tof q61 q285 q286
tof q285 q61
tof q60 q284 q285
tof q284 q60
tof q59 q283 q284
tof q283 q59
tof q58 q282 q283
tof q282 q58
tof q57 q281 q282
tof q281 q57
tof q56 q280 q281
tof q280 q56
tof q55 q279 q280
tof q279 q55
tof q54 q278 q279
tof q278 q54
tof q53 q277 q278
tof q277 q53
tof q52 q276 q277
tof q276 q52
tof q51 q275 q276
tof q275 q51
tof q50 q274 q275
tof q274 q50
tof q49 q273 q274
tof q273 q49
tof q48 q272 q273
tof q272 q48
tof q47 q271 q272
tof q271 q47
tof q46 q270 q271
tof q270 q46
tof q45 q269 q270
tof q269 q45
tof q44 q268 q269
tof q268 q44
tof q43 q267 q268
tof q267 q43
tof q42 q266 q267
tof q266 q42
tof q41 q265 q266
tof q265 q41
tof q40 q264 q265
tof q264 q40
tof q39 q263 q264
tof q263 q39
tof q38 q262 q263
tof q262 q38
tof q37 q261 q262
tof q261 q37
tof q36 q260 q261
tof q260 q36
tof q35 q259 q260
tof q259 q35
tof q34 q258 q259
tof q258 q34
tof q33 q257 q258
tof q257 q33
tof q32 q256 q257
tof q257 q258
tof q258 q259
tof q259 q260
tof q260 q261
tof q261 q262
tof q262 q263
tof q263 q264
tof q264 q265
tof q265 q266
tof q266 q267
tof q267 q268
tof q268 q269
tof q269 q270
tof q270 q271
tof q271 q272
tof q272 q273
tof q273 q274
tof q274 q275
tof q275 q276
tof q276 q277
tof q277 q278
tof q278 q279
tof q279 q280
tof q280 q281
tof q281 q282
tof q282 q283
tof q283 q284
tof q284 q285
tof q285 q286
tof q286 q287
tof q256 q32
tof q257 q33
tof q258 q34
tof q259 q35
tof q260 q36
tof q261 q37
tof q262 q38
tof q263 q39
tof q264 q40
tof q265 q41
tof q266 q42
tof q267 q43
tof q268 q44
tof q269 q45
tof q270 q46
tof q271 q47
tof q272 q48
tof q273 q49
tof q274 q50
tof q275 q51
tof q276 q52
tof q277 q53
tof q278 q54
tof q279 q55
tof q280 q56
tof q281 q57
tof q282 q58
tof q283 q59
tof q284 q60
tof q285 q61
tof q286 q62
tof q287 q63
tof q35 q288
tof q36 q289
tof q37 q290
tof q38 q291
tof q39 q292
tof q40 q293
tof q41 q294
tof q42 q295
tof q43 q296
tof q44 q297
tof q45 q298
tof q46 q299
tof q47 q300
tof q48 q301
tof q49 q302
tof q50 q303
tof q51 q304
tof q52 q305
tof q53 q306
tof q54 q307
tof q55 q308
tof q56 q309
tof q57 q310
tof q58 q311
tof q59 q312
tof q60 q313
tof q61 q314
tof q62 q315
tof q63 q316
tof q289 q1
tof q290 q2
tof q291 q3
tof q292 q4
tof q293 q5
tof q294 q6
tof q295 q7
tof q296 q8
tof q297 q9
tof q298 q10
tof q299 q11
tof q300 q12
tof q301 q13
tof q302 q14
tof q303 q15
tof q304 q16
tof q305 q17
tof q306 q18
tof q307 q19
tof q308 q20
tof q309 q21
tof q310 q22
tof q311 q23
tof q312 q24
tof q313 q25
tof q314 q26
tof q315 q27
tof q316 q28
tof q317 q29
tof q318 q30
tof q319 q31
tof q318 q319
tof q317 q318
tof q316 q317
tof q315 q316
tof q314 q315
tof q313 q314
tof q312 q313
tof q311 q312
tof q310 q311
tof q309 q310
tof q308 q309
tof q307 q308
tof q306 q307
tof q305 q306
tof q304 q305
tof q303 q304
tof q302 q303
tof q301 q302
tof q300 q301
tof q299 q300
tof q298 q299
tof q297 q298
tof q296 q297
tof q295 q296
tof q294 q295
tof q293 q294
tof q292 q293
tof q291 q292
tof q290 q291
tof q289 q290
tof q0 q288 q289
tof q1 q289 q290
tof q2 q290 q291
tof q3 q291 q292
tof q4 q292 q293
tof q5 q293 q294
tof q6 q294 q295
tof q7 q295 q296
tof q8 q296 q297
tof q9 q297 q298
tof q10 q298 q299
tof q11 q299 q300
tof q12 q300 q301
tof q13 q301 q302
tof q14 q302 q303
tof q15 q303 q304
tof q16 q304 q305
tof q17 q305 q306
tof q18 q306 q307
tof q19 q307 q308
tof q20 q308 q309
tof q21 q309 q310
tof q22 q310 q311
tof q23 q311 q312
tof q24 q312 q313
tof q25 q313 q314
tof q26 q314 q315
tof q27 q315 q316
tof q28 q316 q317
tof q29 q317 q318
tof q30 q318 q319
tof q319 q31
tof q30 q318 q319
tof q318 q30
tof q29 q317 q318
tof q317 q29
tof q28 q316 q317
tof q316 q28
tof q27 q315 q316
tof q315 q27
tof q26 q314 q315
tof q314 q26
tof q25 q313 q314
tof q313 q25
tof q24 q312 q313
tof q312 q24
tof q23 q311 q312
tof q311 q23
tof q22 q310 q311
tof q310 q22
tof q21 q309 q310
tof q309 q21
tof q20 q308 q309
tof q308 q20
tof q19 q307 q308
tof q307 q19
tof q18 q306 q307
tof q306 q18
tof q17 q305 q306
tof q305 q17
tof q16 q304 q305
tof q304 q16
tof q15 q303 q304
tof q303 q15
tof q14 q302 q303
tof q302 q14
tof q13 q301 q302
tof q301 q13
tof q12 q300 q301
tof q300 q12
tof q11 q299 q300
tof q299 q11
tof q10 q298 q299
tof q298 q10
tof q9 q297 q298
tof q297 q9
tof q8 q296 q297
tof q296 q8
tof q7 q295 q296
tof q295 q7
tof q6 q294 q295
tof q294 q6
tof q5 q293 q294
tof q293 q5
tof q4 q292 q293
tof q292 q4
tof q3 q291 q292
tof q291 q3
tof q2 q290 q291
tof q290 q2
tof q1 q289 q290
tof q289 q1
tof q0 q288 q289
tof q289 q290
tof q290 q291
tof q291 q292
tof q292 q293
tof q293 q294
tof q294 q295
tof q295 q296
tof q296 q297
tof q297 q298
tof q298 q299
tof q299 q300
tof q300 q301
tof q301 q302
tof q302 q303
tof q303 q304
tof q304 q305
tof q305 q306
tof q306 q307
tof q307 q308
tof q308 q309
tof q309 q310
tof q310 q311
tof q311 q312
tof q312 q313
tof q313 q314
tof q314 q315
tof q315 q316
tof q316 q317
tof q317 q318
tof q318 q319
tof q288 q0
tof q289 q1
tof q290 q2
tof q291 q3
tof q292 q4
tof q293 q5
tof q294 q6
tof q295 q7
tof q296 q8
tof q297 q9
tof q298 q10
tof q299 q11
tof q300 q12
tof q301 q13
tof q302 q14
tof q303 q15
tof q304 q16
tof q305 q17
tof q306 q18
tof q307 q19
tof q308 q20
tof q309 q21
tof q310 q22
tof q311 q23
tof q312 q24
tof q313 q25
tof q314 q26
tof q315 q27
tof q316 q28
tof q317 q29
tof q318 q30
tof q319 q31
END
