/* Included inside EvaluationVisitor. Do not include directly. */
    std::any visitDiracs(ExtendedDiracParser::DiracsContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            std::vector<std::string> result;
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                result = std::any_cast<std::vector<std::string>>(visit(ctx->diracs()));
            }
            result.push_back(std::any_cast<std::string>(visit(ctx->dirac())));
            return result;
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->diracs() == nullptr) { // RULE: dirac
                return std::any_cast<strs2split_t>(visit(ctx->dirac()));
            } else { // RULE: diracs ',' dirac
                auto vec0 = std::any_cast<strs2split_t>(visit(ctx->diracs()));
                auto vec1 = std::any_cast<strs2split_t>(visit(ctx->dirac()));
                vec0.insert(vec0.end(), vec1.begin(), vec1.end());
                return vec0;
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->diracs() == nullptr) { // RULE: dirac
                return visit(ctx->dirac());
            } else { // RULE: diracs ',' dirac
                return std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->diracs())) || std::any_cast<AUTOQ::Automata<Symbol>>(visit(ctx->dirac()));
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<relation_t>(visit(ctx->dirac()));
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<std::string>(visit(ctx->dirac()));
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<std::vector<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>>(visit(ctx->dirac()));
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->diracs() != nullptr) { // RULE: diracs, dirac
                THROW_AUTOQ_ERROR("After expansion, diracs should contain only one dirac.");
            }
            return std::any_cast<std::vector<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>>(visit(ctx->dirac()));
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitDirac(ExtendedDiracParser::DiracContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            if (ctx->dirac() == nullptr) { // RULE: term
                return std::any_cast<std::string>(visit(ctx->term()));
            } else if (ctx->ADD() != nullptr) { // RULE: dirac + term
                auto str1 = std::any_cast<std::string>(visit(ctx->dirac()));
                auto str2 = std::any_cast<std::string>(visit(ctx->term()));
                return str1 + " + " + str2;
            } else if (ctx->SUB() != nullptr) { // RULE: dirac - term
                auto str1 = std::any_cast<std::string>(visit(ctx->dirac()));
                auto str2 = std::any_cast<std::string>(visit(ctx->term()));
                return str1 + " +- " + str2;
            } else {
                THROW_AUTOQ_ERROR("Unsupported syntax!");
            }
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            if (ctx->dirac() == nullptr) { // RULE: term
                strs2split_t Vstrs;
                Vstrs.push_back(std::any_cast<strsplit_t>(visit(ctx->term())));
                return Vstrs;
            } else if (ctx->SUB() != nullptr) { // RULE: dirac - term
                THROW_AUTOQ_ERROR("All subtractions should be replaced with additions followed by negations.");
            } else { // RULE: dirac + term
                auto Vstrs = std::any_cast<strs2split_t>(visit(ctx->dirac()));
                Vstrs.push_back(std::any_cast<strsplit_t>(visit(ctx->term())));
                return Vstrs;
            }
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            if (ctx->dirac() == nullptr) { // RULE: term
                return std::any_cast<std::string>(visit(ctx->term()));
            } else if (ctx->SUB() != nullptr) { // RULE: dirac - term
                THROW_AUTOQ_ERROR("All subtractions should be replaced with additions followed by negations.");
            } else { // RULE: dirac + term
                auto str1 = std::any_cast<std::string>(visit(ctx->dirac()));
                auto str2 = std::any_cast<std::string>(visit(ctx->term()));
                return str1 + " + " + str2;
            }
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            if (ctx->dirac() == nullptr) { // RULE: term
                return std::any_cast<relation_t>(visit(ctx->term()));
            } else if (ctx->SUB() != nullptr) { // RULE: dirac - term
                THROW_AUTOQ_ERROR("All subtractions should be replaced with additions followed by negations.");
            } else { // RULE: dirac + term
                auto relation1 = std::any_cast<relation_t>(visit(ctx->dirac()));
                auto relation2 = std::any_cast<relation_t>(visit(ctx->term()));
                int i = 0;
                for (const auto &chars: relation2.first) {
                    relation1.first.at(i).insert(*chars.begin());
                    i++;
                }
                for (const auto &ineq: relation2.second) {
                    relation1.second.insert(ineq);
                }
                return relation1;
            }
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            if (ctx->dirac() == nullptr) { // RULE: term
                return std::any_cast<std::string>(visit(ctx->term()));
            } else if (ctx->SUB() != nullptr) { // RULE: dirac - term
                THROW_AUTOQ_ERROR("All subtractions should be replaced with additions followed by negations.");
            } else { // RULE: dirac + term
                auto str1 = std::any_cast<std::string>(visit(ctx->dirac()));
                auto str2 = std::any_cast<std::string>(visit(ctx->term()));
                return str1 + " + " + str2;
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            if (ctx->dirac() == nullptr) { // RULE: term
                std::vector<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>> result;
                result.push_back(std::any_cast<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>(visit(ctx->term())));
                return result;
            } else if (ctx->SUB() != nullptr) { // RULE: dirac - term
                THROW_AUTOQ_ERROR("All subtractions should be replaced with additions followed by negations.");
            } else { // RULE: dirac + term
                auto result1 = std::any_cast<std::vector<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>>(visit(ctx->dirac()));
                auto result2 = std::any_cast<std::tuple<std::string, std::vector<varconS_t>, std::vector<std::string>>>(visit(ctx->term()));
                result1.push_back(result2);
                return result1;
            }
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            if (ctx->dirac() == nullptr) { // RULE: term
                std::vector<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>> result;
                result.push_back(std::any_cast<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>(visit(ctx->term())));
                return result;
            } else if (ctx->SUB() != nullptr) { // RULE: dirac - term
                THROW_AUTOQ_ERROR("All subtractions should be replaced with additions followed by negations.");
            } else { // RULE: dirac + term
                auto result1 = std::any_cast<std::vector<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>>(visit(ctx->dirac()));
                auto result2 = std::any_cast<std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>>(visit(ctx->term()));
                result1.push_back(result2);
                return result1;
            }
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }

    std::any visitTerm(ExtendedDiracParser::TermContext *ctx) override {
        if (mode == EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT) {
            auto vstr = ctx->VStr->getText();
            std::string vstr2;
            for (size_t i=0; i<vstr.length(); i++) {
                if (i+1<vstr.length() && vstr.at(i+1)=='\'') {
                    vstr2.push_back(vstr.at(i)-'a'+'A'); // capitalize the bit complement
                    i++;
                } else {
                    vstr2.push_back(vstr.at(i));
                }
            }
            if (ctx->varcons() == nullptr) { // C=STR BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>((ctx->complex() == nullptr ? (ctx->SUB() != nullptr ? "-1" : "") : ctx->complex()->getText()) + "|" + vstr2 + "⟩");
            } else { // C=STR SUM varcons BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>((ctx->complex() == nullptr ? (ctx->SUB() != nullptr ? "-1" : "") : ctx->complex()->getText()) + "∑" + ctx->varcons()->getText() + "|" + vstr2 + "⟩");
            }
        } else if (mode == COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES) {
            strsplit_t intervals;
            std::map<char, int> localVar2len;
            if (ctx->varcons() != nullptr) {
                localVar2len = std::any_cast<std::map<char, int>>(visit(ctx->varcons()));
            }
            int len = 0;
            for (const auto &c : ctx->VStr->getText()) {
                if ((c == '0') || (c == '1')) {
                    len++;
                    continue;
                }
                auto it = localVar2len.find(static_cast<char>(std::tolower(c)));
                if (it != localVar2len.end()) {
                    intervals.push_back(unitsplit_t(len, len+it->second));
                    len += it->second;
                } else {
                    it = globalVar2len.find(static_cast<char>(std::tolower(c)));
                    if (it != globalVar2len.end()) {
                        intervals.push_back(unitsplit_t(len, len+it->second));
                        len += it->second;
                    } else {
                        THROW_AUTOQ_ERROR("Undefined variable!");
                    }
                }
            }
            return intervals;
        } else if (mode == REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT) {
            /***************************************************************/
            // Check if there is some local variable using global characters.
            // If yes, then we need to change the local variable's name.
            std::map<char, int> localVar2len;
            if (ctx->varcons() != nullptr) {
                localVar2len = std::any_cast<std::map<char, int>>(visit(ctx->varcons()));
            }
            std::map<char, char> changeLocalVar2;
            for (const auto &[k, v] : localVar2len) {
                if (usedVars.find(k) == usedVars.end()) { // if this local variable has not been used before,
                    usedVars.insert(k); // keep the original name
                } else { // otherwise,
                    for (char newCh = 'a'; newCh <= 'z'; newCh++) { // Find a new character for this local variable
                        if (usedVars.find(newCh) == usedVars.end()) {
                            changeLocalVar2[k] = newCh;
                            usedVars.insert(newCh);
                            break;
                        }
                        if (newCh == 'z') {
                            THROW_AUTOQ_ERROR("chars not enough!!!");
                        }
                    }
                }
            }
            /***************************************************************/
            std::string vstr = ctx->VStr->getText();
            std::string vstr2; // the rewritten output
            remember_the_lengths_of_each_unit_position.clear();
            /*************************************************/
            currentSplit_t completeCurrentSplit; // fill the gaps such that all units except the last are covered
            int connectionIndex = 0;
            for (const auto &[l, r] : currentSplit) {
                if (connectionIndex < l) {
                    completeCurrentSplit.push_back(unitsplit_t(connectionIndex, l));
                }
                completeCurrentSplit.push_back(unitsplit_t(l, r));
                connectionIndex = r;
            }
            completeCurrentSplit.push_back(unitsplit_t(connectionIndex, -1)); // indicate checking the last remaining part not classified as a unit (if it exists)
            /***********************************************/
            std::map<std::string, char> localVal2const;
            for (const auto &[l, r] : completeCurrentSplit) {
                if (r == -1 || // the last remaining part not classified as a unit must be a constant
                    vstr.at(0)=='0' || vstr.at(0)=='1') {
                    if (vstr.empty()) continue; // reject if there is no remaining part
                    std::string this_constant_string = ((r == -1) ? vstr : vstr.substr(0, r-l));
                    if (!std::all_of(this_constant_string.begin(), this_constant_string.end(), [](char ch) { return ch == '0' || ch == '1'; })) {
                        THROW_AUTOQ_ERROR("Not aligned!");
                    }
                    if (r != -1) vstr.erase(0, r-l);
                    auto it = localVal2const.find(this_constant_string);
                    if (it != localVal2const.end()) {
                        vstr2 += it->second;
                    } else {
                        // Find a character for this constant!
                        char ch='a';
                        for (; ch<='z'; ch++) {
                            if (usedVars.find(ch) == usedVars.end()) {
                                usedVars.insert(ch);
                                break;
                            }
                            if (ch == 'z') {
                                THROW_AUTOQ_ERROR("chars not enough!!!");
                            }
                        }
                        vstr2 += ch;
                        localVal2const[this_constant_string] = ch;
                    }
                    remember_the_lengths_of_each_unit_position.push_back(this_constant_string.length());
                } else { // char or CHAR
                    char ch = std::tolower(vstr.at(0)); // IMPORTANT!
                    auto it = globalVar2len.find(static_cast<char>(ch));
                    if (it != globalVar2len.end()) { // is a global variable, whose name cannot be changed
                        vstr2 += vstr.at(0);
                        remember_the_lengths_of_each_unit_position.push_back(it->second);
                    } else { // must be a local variable
                        auto it = localVar2len.find(static_cast<char>(ch));
                        if (it == localVar2len.end()) {
                            THROW_AUTOQ_ERROR("Undefined variable!");
                        } else if (it->second != r - l) {
                            THROW_AUTOQ_ERROR("Not aligned!");
                        } else { // check if it has already been renamed
                            auto it2 = changeLocalVar2.find(ch);
                            if (it2 == changeLocalVar2.end()) { // not renamed
                                vstr2 += vstr.at(0);
                            } else { // has been renamed
                                if (vstr.at(0) == ch) { // lowercase
                                    vstr2 += vstr.at(0);
                                } else { // uppercase (bit complemented)
                                    vstr2 += it2->second - 'a' + 'A';
                                }
                            }
                            remember_the_lengths_of_each_unit_position.push_back(it->second);
                        }
                    }
                    vstr.erase(vstr.begin());
                }
            }

            // C=STR BAR VStr=STR RIGHT_ANGLE_BRACKET
            // C=STR SUM varcons BAR VStr=STR RIGHT_ANGLE_BRACKET
            // two rules processed together
            auto vc = (ctx->varcons() == nullptr) ? "" : ctx->varcons()->getText(); // may contain capitalized bit complement
            auto ket = vstr2;
            for (auto *str : {&vc, &ket}) {
                for (auto &ch : *str) {
                    auto it = changeLocalVar2.find(static_cast<char>(std::tolower(ch)));
                    if (it != changeLocalVar2.end()) {
                        if (std::isupper(ch)) {
                            ch = it->second - 'a' + 'A';
                        } else { // std::islower(ch)
                            ch = it->second;
                        }
                    }
                }
            }
            for (const auto &[c, v] : localVal2const) {
                if (vc.empty()) {
                    vc += std::string{v} + "=" + c;
                } else {
                    vc += ", " + std::string{v} + "=" + c;
                }
            }
            return (ctx->complex() == nullptr ? (ctx->SUB() != nullptr ? "-1" : "") : ctx->complex()->getText()) + ((!vc.empty()) ? ("∑" + vc) : "") + "|" + ket + "⟩";
        } else if (mode == COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION) {
            unit2vars_t first;
            auto str = ctx->VStr->getText();
            for (auto ch : str) {
                first.push_back(vars_t{static_cast<char>(std::tolower(ch))});
            }
            ineqS_t second;
            if (ctx->varcons() != nullptr) {
                second = std::any_cast<ineqS_t>(visit(ctx->varcons()));
            }
            return relation_t{first, second};
        } else if (mode == REORDER_UNITS_BY_THE_GROUP) {
            std::string vstr = ctx->VStr->getText();
            std::vector<bool> moved(vstr.length(), false);
            std::string vstr2;
            for (size_t i=0; i<vstr.length(); i++) {
                if (!moved.at(i)) {
                    for (const auto &cc : currentPerm) {
                        if (std::find(cc.begin(), cc.end(), i) != cc.end()) {
                            for (auto j : cc) {
                                vstr2.push_back(vstr.at(j));
                                moved.at(j) = true;
                            }
                            break;
                        }
                    }
                    if (!moved.at(i)) { // NOTE: This patch deals with the case when a character is not in any connected component.
                        vstr2.push_back(vstr.at(i));
                        moved.at(i) = true;
                    }
                }
            }
            if (ctx->varcons() == nullptr) { // C=STR BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>((ctx->complex() == nullptr ? (ctx->SUB() != nullptr ? "-1" : "") : ctx->complex()->getText()) + "|" + vstr2 + "⟩");
            } else { // C=STR SUM varcons BAR VStr=STR RIGHT_ANGLE_BRACKET
                return std::any_cast<std::string>((ctx->complex() == nullptr ? (ctx->SUB() != nullptr ? "-1" : "") : ctx->complex()->getText()) + "∑" + ctx->varcons()->getText() + "|" + vstr2 + "⟩");
            }
        } else if (mode == SET_BRACES_IS_TENSOR_DECOMPOSED_INTO_GROUPS) {
            auto vecVarconS2 = ctx->varcons() == nullptr ? varconS_t() : std::any_cast<varconS_t>(visit(ctx->varcons()));
            std::vector<varconS_t> vecVarconS;
            std::vector<std::string> groups;
            auto vstr = ctx->VStr->getText();
            std::vector<int> selectedCC;
            for (size_t i=0; i < vstr.length(); i += selectedCC.size()) {
                selectedCC.clear();
                for (const auto &cc : currentPerm) { // Notice that the indices in currentPerm are no longer valid here. We only want those "fixpoint" indices!
                    if (std::find(cc.begin(), cc.end(), i) != cc.end()) {
                        selectedCC = cc; // find the connected component that contains the index i
                        break; // one index belongs to at most one connected component
                    }
                }
                if (selectedCC.empty()) { // this character is a group itself
                    selectedCC = {static_cast<int>(i)};
                } // NOTE: This patch deals with the case when a character is not in any connected component.
                auto str = vstr.substr(i, selectedCC.size());
                varconS_t varconS;
                for (char ch : str) {
                    ch = std::tolower(ch);
                    for (const auto &varcon : vecVarconS2) {
                        /* varcon: BAR V=STR BAR EQ N=STR {isNonZero($N.text)}?
                                    | V=STR EQ CStr=STR
                                    | ineq
                                    ;
                        */
                        if (varcon.first.find(ch) != varcon.first.end()) {
                            varconS.push_back(varcon);
                        }
                    }
                }
                vecVarconS.push_back(varconS);
                groups.push_back(str);
            }
            return std::make_tuple((ctx->complex() == nullptr ? "1" : ctx->complex()->getText()), vecVarconS, groups);
        } else if (mode == SHUFFLE_UNITS_IN_A_GROUP_WRT_QUBITS_AND_CONSTRUCT_LSTA_FINALLY) {
            // std::tuple<std::string, std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>, std::string>
            //            coefficient,                varcons: <len,   control vars,     inequalities>,          ket>
            auto coefficient = (ctx->complex() == nullptr ? "1" : ctx->complex()->getText());
            std::optional<std::tuple<int, std::set<char>, ineqS_t, eqs_t>> varcons;
            auto ket = ctx->VStr->getText();
            if (ctx->varcons() != nullptr) {
                varcons = std::any_cast<std::tuple<int, std::set<char>, ineqS_t, eqs_t>>(visit(ctx->varcons()));
            }
            return std::make_tuple(coefficient, varcons, ket);
        } else {
            THROW_AUTOQ_ERROR("Unsupported mode!");
        }
    }
