/*****************************************************************************
 *  AUTOQ Timbuk parser – Extended Dirac notation (.hsl).
 *
 *  Parses "Extended Dirac" via ANTLR; single and multi-stream .hsl.
 *
 *  Main functions: parse_extended_dirac_from_istream,
 *  parse_n_extended_diracs_from_istream, parse_extended_dirac,
 *  parse_n_extended_diracs.
 *****************************************************************************/
#ifndef AUTOQ_PARSING_TIMBUK_PARSER_DIRAC_HH
#define AUTOQ_PARSING_TIMBUK_PARSER_DIRAC_HH

template <typename Symbol, typename Symbol2>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::parse_extended_dirac_from_istream(std::istream *is, bool &do_not_throw_term_undefined_error, const std::map<std::string, AUTOQ::Complex::Complex> &constants, const std::string &predicateConstraints) {
    bool start_transitions = false;
    std::string line;
    std::string extended_dirac;

    while (std::getline(*is, line))
    {
		line = AUTOQ::String::trim(line);
		if (line.empty())
            continue;
		else if (!start_transitions)
        {
            if (std::regex_search(line, std::regex("Extended +Dirac")))
            {
                start_transitions = true;
                continue;
            } else {
                THROW_AUTOQ_ERROR("The section \"Extended Dirac\" should be declared first before specifying the states.");
            }
        } else {
            extended_dirac += line + '\n';
        }
    }

    /****************************************
    * Parse the Extended Dirac with ANTLR v4.
    *****************************************/
    EvaluationVisitor<Symbol> visitor({constants}, {predicateConstraints});
    auto extended_dirac2 = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac));
    visitor.mode = EvaluationVisitor<Symbol>::COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES;
    typename EvaluationVisitor<Symbol>::segment2split_t segment2split = std::any_cast<typename EvaluationVisitor<Symbol>::segment2split_t>(visitor.let_visitor_parse_string(extended_dirac2));
    visitor.mode = EvaluationVisitor<Symbol>::REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT;
    visitor.segment2split = segment2split;
    auto extended_dirac3 = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac2));
    visitor.mode = EvaluationVisitor<Symbol>::COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION;
    auto segment2perm = std::any_cast<typename EvaluationVisitor<Symbol>::segment2perm_t>(visitor.let_visitor_parse_string(extended_dirac3));
    visitor.mode = EvaluationVisitor<Symbol>::REORDER_UNITS_BY_THE_GROUP;
    visitor.segment2perm = segment2perm;
    auto afterrewrite = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac3));
    visitor.mode = EvaluationVisitor<Symbol>::EVALUATE_EACH_SET_BRACES_TO_LSTA;
    visitor.segment2perm = segment2perm;
    visitor.do_not_throw_term_undefined_error = do_not_throw_term_undefined_error;
    auto final = std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visitor.let_visitor_parse_string(afterrewrite)).at(0);
    if (!visitor.do_not_throw_term_undefined_error || visitor.encountered_term_undefined_error) {
        do_not_throw_term_undefined_error = false;
    }
    return final;
}
template <typename Symbol, typename Symbol2>
std::pair<std::vector<AUTOQ::Automata<Symbol>>, std::vector<int>>
AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::parse_n_extended_diracs_from_istream(std::vector<std::istream*> isVec,
                                                                              const std::vector<std::map<std::string, AUTOQ::Complex::Complex>> &constantsVec,
                                                                              const std::vector<std::string> &predicateConstraintsVec) {
    std::vector<std::string> extended_dirac(isVec.size());
    std::vector<std::vector<std::string>> exprs(isVec.size());
    int i = 0;
    for (std::istream *is : isVec) {
        bool start_transitions = false;
        std::string line;
        while (std::getline(*is, line))
        {
            line = AUTOQ::String::trim(line);
            if (line.empty()) { continue; }
            else if (!start_transitions)
            {
                if (std::regex_search(line, std::regex("Extended +Dirac")))
                {
                    start_transitions = true;
                    continue;
                } else {
                    THROW_AUTOQ_ERROR("The section \"Extended Dirac\" should be declared first before specifying the states.");
                }
            } else { // processing states
                extended_dirac[i] += line + '\n'; // Do NOT miss '\n' for the ANTLR to parse correctly with '\n'
            }
        }
        EvaluationVisitor<Symbol, Symbol2> visitor({constantsVec[i]}, {predicateConstraintsVec[i]});
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::EXPAND_POWER_AND_DIRACS_AND_REWRITE_COMPLEMENT;
        auto extended_dirac2 = std::any_cast<std::string>(visitor.let_visitor_parse_string(extended_dirac[i]));
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::SPLIT_TENSORED_EXPRESSION_INTO_VECTOR_OF_SETS_WITHOUT_TENSOR;
        exprs[i] = std::any_cast<std::vector<std::string>>(visitor.let_visitor_parse_string(extended_dirac2)); // now we assume it does NOT contain SETMINUS
        /**/
        i++;
    }
    for (size_t i=1; i<exprs.size(); i++) {
        if (exprs[i-1].size() != exprs[i].size()) {
            AUTOQ::Util::Log::error("[ERROR] The 1st list of expressions: " + AUTOQ::Util::Convert::ToString(exprs[i-1]));
            AUTOQ::Util::Log::error("[ERROR] The 2nd list of expressions: " + AUTOQ::Util::Convert::ToString(exprs[i]));
            THROW_AUTOQ_ERROR("There are two *.hsl files not aligned!");
        }
    }

    std::vector<AUTOQ::Automata<Symbol>> results;
    std::vector<int> qubit_permutation;
    for (size_t i=0; i<exprs[0].size(); ++i) {
        auto new_composited_expression = exprs[0][i];
        for (size_t j=1; j<exprs.size(); j++)
            new_composited_expression += " ; " + exprs[j][i];
        EvaluationVisitor<Symbol, Symbol2> visitor(constantsVec, predicateConstraintsVec); // any pair of constants and predicates can do
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::COLLECT_KETS_AND_COMPUTE_UNIT_DECOMPOSITION_INDICES;
        typename EvaluationVisitor<Symbol, Symbol2>::segment2split_t segment2split = std::any_cast<typename EvaluationVisitor<Symbol, Symbol2>::segment2split_t>(visitor.let_visitor_parse_string(new_composited_expression));
        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::REWRITE_BY_UNIT_INDICES_AND_MAKE_ALL_VARS_DISTINCT;
        visitor.segment2split = segment2split;
        auto extended_diracC = std::any_cast<std::string>(visitor.let_visitor_parse_string(new_composited_expression));

        /*********************************************************************************/
        int counter = 0;
        std::vector<std::vector<int>> expand_to_qubits;
        for (int len : visitor.remember_the_lengths_of_each_unit_position) {
            std::vector<int> qubits(len);
            std::iota(qubits.begin(), qubits.end(), counter); // Fill with 0, 1, ..., len-1
            expand_to_qubits.push_back(qubits);
            counter += len;
        }
        /*********************************************************************************/

        visitor.mode = EvaluationVisitor<Symbol, Symbol2>::COMPUTE_CONNECTED_UNITS_INTO_A_GROUP_RELATION;
        auto segment2perm = std::any_cast<typename EvaluationVisitor<Symbol, Symbol2>::segment2perm_t>(visitor.let_visitor_parse_string(extended_diracC));
        if (segment2perm.size() != 1) {
            THROW_AUTOQ_ERROR("We only process one tensor segment at a time.");
        }
        auto base = qubit_permutation.size();
        for (const auto &cc : *segment2perm.begin()) {
            for (size_t i=0; i<expand_to_qubits.at(*cc.begin()).size(); i++) {
                for (auto g : cc) {
                    qubit_permutation.push_back(base + expand_to_qubits.at(g).at(i));
                }
            }
        }

        std::stringstream ss(extended_diracC);
        std::string item;
        int j = -1;
        while (std::getline(ss, item, ';')) {
            std::string trimmed = AUTOQ::String::trim(item);
            if (!trimmed.empty()) {
                j++;
                EvaluationVisitor<Symbol> visitor({constantsVec[j]}, {predicateConstraintsVec[j]});
                visitor.mode = EvaluationVisitor<Symbol>::REORDER_UNITS_BY_THE_GROUP;
                visitor.segment2perm = segment2perm;
                auto afterrewrite = std::any_cast<std::string>(visitor.let_visitor_parse_string(trimmed));
                visitor.mode = EvaluationVisitor<Symbol>::EVALUATE_EACH_SET_BRACES_TO_LSTA;
                visitor.segment2perm = segment2perm;
                auto final = std::any_cast<std::vector<AUTOQ::Automata<Symbol>>>(visitor.let_visitor_parse_string(afterrewrite)).at(0);
                if (i == 0)
                    results.push_back(final);
                else
                    results.at(j) = results.at(j).operator*(final);
            } else {
                THROW_AUTOQ_ERROR("Impossible case!");
            }
        }
    }

    size_t N = qubit_permutation.size();
    std::vector<int> inverse_permutation(N);
    for (size_t i = 0; i < N; ++i) {
        inverse_permutation[qubit_permutation[i]] = i;
    }
    return std::make_pair(results, inverse_permutation);
}

template <typename Symbol>
AUTOQ::Automata<Symbol> parse_extended_dirac(const std::string& str, const std::map<std::string, Complex> &constants, const std::string &predicateConstraints, bool &do_not_throw_term_undefined_error) {
    std::istringstream inputStream(str);
    return AUTOQ::Parsing::TimbukParser<Symbol>::parse_extended_dirac_from_istream(&inputStream, do_not_throw_term_undefined_error, constants, predicateConstraints);
}
template <typename Symbol, typename Symbol2>
std::pair<std::vector<AUTOQ::Automata<Symbol>>, std::vector<int>> parse_n_extended_diracs(const std::vector<std::string>& strVec, const std::vector<std::map<std::string, Complex>> &constantsVec, const std::vector<std::string> &predicateConstraintsVec) {
    std::vector<std::istringstream> streamStorage;
    std::vector<std::istream*> istreamVec;
    streamStorage.reserve(strVec.size());
    istreamVec.reserve(strVec.size());
    for (const auto& str : strVec) {
        streamStorage.emplace_back(str);
        istreamVec.push_back(&streamStorage.back());
    }
    return AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::parse_n_extended_diracs_from_istream(istreamVec, constantsVec, predicateConstraintsVec);
}

#endif
