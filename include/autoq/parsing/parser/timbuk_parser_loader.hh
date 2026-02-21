/*****************************************************************************
 *  AUTOQ Timbuk parser – loading automata from file paths.
 *
 *  Reads file contents, strips line comments, parses Constants (if present),
 *  then dispatches by extension (.aut / .lsta / .hsl) to parse_timbuk,
 *  parse_automaton, or parse_extended_dirac. Also supports reading two
 *  automata plus optional loop-invariant files (find_all_loop_invariants).
 *  Depends on timbuk_parser_util.hh, timbuk_parser_grammar.hh,
 *  timbuk_parser_transitions.hh, timbuk_parser_dirac.hh.
 *
 *  Main functions (templates, defined in this header):
 *  - TimbukParser::ReadAutomaton(filepath)           Single file → one automaton.
 *  - TimbukParser::ReadAutomaton(filepath, do_not_throw...)  Same with error flag.
 *  - TimbukParser::ReadTwoAutomata(path1, path2, circuitPath)  Two automata
 *    (and optionally extra paths from circuit’s loop-invariant comments).
 *****************************************************************************/
#ifndef AUTOQ_PARSING_TIMBUK_PARSER_LOADER_HH
#define AUTOQ_PARSING_TIMBUK_PARSER_LOADER_HH
#include "autoq/parsing/parser/timbuk_parser_util.hh"
#include "autoq/parsing/parser/timbuk_parser_grammar.hh"
#include "autoq/parsing/parser/timbuk_parser_transitions.hh"
#include "autoq/parsing/parser/timbuk_parser_dirac.hh"

template <typename Symbol, typename Symbol2>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadAutomaton(const std::string& filepath) {
    bool do_not_throw_term_undefined_error = false;
    return AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadAutomaton(filepath, do_not_throw_term_undefined_error);
}
template <typename Symbol, typename Symbol2>
AUTOQ::Automata<Symbol> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadAutomaton(const std::string& filepath, bool &do_not_throw_term_undefined_error) {
try {
    AUTOQ::Automata<Symbol> result;
    std::string automaton, constraints;
    std::string fileContents = AUTOQ::Util::ReadFile(filepath);
    AUTOQ::Parsing::strip_line_comments(fileContents);
    std::map<std::string, AUTOQ::Complex::Complex> constants;
    if (!boost::algorithm::ends_with(filepath, ".aut") && fileContents.find("Constants") != std::string::npos) {
        AUTOQ::Parsing::parse_constants_section(fileContents, constants);
        AUTOQ::Parsing::unify_complex_k(constants);
    }
    std::tie(automaton, constraints) = AUTOQ::Parsing::split_automaton_and_constraints(fileContents);
    if (boost::algorithm::ends_with(filepath, ".lsta")) {
        std::map<std::string, std::string> dummy_predicates;
        result = parse_automaton<Symbol>(automaton, constants, dummy_predicates, do_not_throw_term_undefined_error);
    } else if (boost::algorithm::ends_with(filepath, ".aut")) {
        result = parse_timbuk<Symbol>(automaton);
    } else if (boost::algorithm::ends_with(filepath, ".hsl")) {
        result = parse_extended_dirac<Symbol>(automaton, constants, constraints, do_not_throw_term_undefined_error);
    } else {
        THROW_AUTOQ_ERROR("The filename extension is not supported.");
    }

    if constexpr (std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>) {
        std::stringstream ss(AUTOQ::String::trim(constraints));
        std::string constraint;
        while (std::getline(ss, constraint, '\n')) {
            result.constraints += EvaluationVisitor<>::ConstraintParser(constraint, constants).getSMTexpression();
        }
        if (!result.constraints.empty())
            result.constraints = "(and " + result.constraints + ")";
        else
            result.constraints = "true";
    }
    return result;
} catch (AutoQError &e) {
    AUTOQ::Util::Log::error(e.what());
    THROW_AUTOQ_ERROR("(while parsing the automaton: " + filepath + ")");
}
}

template <typename Symbol, typename Symbol2>
std::pair<std::vector<AUTOQ::Automata<Symbol>>, std::vector<int>> AUTOQ::Parsing::TimbukParser<Symbol, Symbol2>::ReadTwoAutomata(const std::string& filepath1, const std::string& filepath2, const std::string &circuitPath) {
try {
    std::vector<std::string> filepathVec = {filepath1, filepath2};
    if (!circuitPath.empty()) {
        auto filepathVec2 = AUTOQ::Parsing::find_all_loop_invariants(circuitPath.c_str());
        filepathVec.insert(filepathVec.end(), filepathVec2.begin(), filepathVec2.end());
    }
    std::vector<std::string> automatonVec(filepathVec.size());
    std::vector<std::string> fileContents(filepathVec.size());
    std::vector<std::string> constraints(filepathVec.size());
    std::vector<std::map<std::string, AUTOQ::Complex::Complex>> constants(filepathVec.size());

    for (size_t i = 0; i < filepathVec.size(); i++) {
        fileContents[i] = AUTOQ::Util::ReadFile(filepathVec[i]);
        AUTOQ::Parsing::strip_line_comments(fileContents[i]);
        if (!boost::algorithm::ends_with(filepathVec[i], ".aut") &&
            (fileContents[i].find("Constants") != std::string::npos ||
             fileContents[i].find("Predicates") != std::string::npos)) {
            AUTOQ::Parsing::parse_constants_section(fileContents[i], constants[i]);
            AUTOQ::Parsing::unify_complex_k(constants[i]);
        }
        std::tie(automatonVec[i], constraints[i]) = AUTOQ::Parsing::split_automaton_and_constraints(fileContents[i]);
    }

    std::vector<AUTOQ::Automata<Symbol>> autVec;
    std::vector<int> qp;
    if (boost::algorithm::ends_with(filepathVec[0], ".hsl") && boost::algorithm::ends_with(filepathVec[1], ".hsl")) {
        std::tie(autVec, qp) = parse_n_extended_diracs<Symbol, Symbol2>(automatonVec, constants, constraints);
    } else if (boost::algorithm::ends_with(filepathVec[0], ".lsta") && boost::algorithm::ends_with(filepathVec[1], ".lsta")) {
        autVec.reserve(filepathVec.size());
        for (size_t i = 0; i < filepathVec.size(); ++i) {
            std::map<std::string, std::string> dummy_predicates;
            bool dummy_do_not_throw = false;
            autVec.emplace_back(parse_automaton<Symbol>(automatonVec[i], constants[i], dummy_predicates, dummy_do_not_throw));
        }
    } else {
        THROW_AUTOQ_ERROR("The filename extension is not supported.");
    }

    int index = 0;
    for (auto &aut : autVec) {
        std::stringstream ss(AUTOQ::String::trim(constraints[index]));
            std::string constraint;
            while (std::getline(ss, constraint, '\n')) {
                aut.constraints += EvaluationVisitor<>::ConstraintParser(constraint, constants[index]).getSMTexpression();
            }
            if (!(aut.constraints).empty())
                aut.constraints = "(and " + aut.constraints + ")";
            else
                aut.constraints = "true";
        index++;
    }
    return std::make_pair(autVec, qp);
} catch (AutoQError &e) {
    AUTOQ::Util::Log::error(e.what());
    THROW_AUTOQ_ERROR("(while parsing the automaton: " + filepath1 + " or " + filepath2 + ")");
}
}

#endif
