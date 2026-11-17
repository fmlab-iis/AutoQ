#include "autoq/loop_summarization.hh"
#include "autoq/aut_description.hh"
#include "autoq/error.hh"
#include "autoq/util/string.hh"
#include <map>
#include <queue>
#include <type_traits>
#include <utility>

namespace {

// tau stores numeric coefficients in front of symbolic_jR / symbolic_jI.
// Concrete parts are already numbers; a symbolic part is an expression.
template<typename Value>
Value scale_by_coefficient(const AUTOQ::Complex::Complex& coefficient, const Value& part) {
    if constexpr (std::is_same_v<Value, AUTOQ::Complex::Complex>) {
        return coefficient * part;
    } else {
        Value result;
        if (coefficient.isZero())
            return result;
        for (const auto& kv : part) {
            auto scaled = kv.second * coefficient;
            scaled.fraction_simplification();
            // 1 coming back as {0, 1, 0, -1, 1} prints as "1/1 *", unlike Complex(1).
            if (scaled.imag().isZero()) {
                try {
                    scaled = AUTOQ::Complex::Complex(scaled.to_rational());
                } catch (const AutoQError&) {
                }
            }
            if (!scaled.isZero())
                result[kv.first] = scaled;
        }
        return result;
    }
}

}  // namespace

template<typename Symbol>
AUTOQ::Automata<Symbol> symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, const AUTOQ::QasmRegexes& re, int num_of_iterations, const std::vector<int>& qubit_permutation);

template<typename Symbol>
void execute_loop(std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params,
                const AUTOQ::QasmRegexes& re, std::smatch match_pieces, const std::vector<int>& qubit_permutation) {
    int start, end;
    try {
        start = std::stoi(match_pieces[2].str());
        end = std::stoi(match_pieces[3].str());
    } catch (const std::out_of_range&) {
        THROW_AUTOQ_ERROR("The bounds of the for loop \"" + match_pieces.str(0) + "\" are too large.");
    }
    int num_of_iterations = end - start + 1;
    if(params["loop"] == "manual"){
        for(int i = start; i <= end; i++){
            for(const std::string& line : loop_body){
                aut.single_gate_execute(line, re, qubit_permutation);
            }
        }
        return;
    }
    if(params["loop"] == "symbolic"){
        aut = symbolic_loop<Symbol>(loop_body, aut, re, num_of_iterations, qubit_permutation);
    }
}

template<typename Symbol>
AUTOQ::Automata<AUTOQ::Symbol::Symbolic> initial_abstraction(AUTOQ::Automata<Symbol>& aut, InverseAbstractionMap<Symbol>& inverse_alpha){
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T;
    AbstractionMap<Symbol> alpha;
    T.name = aut.name + "_loopsum";
    T.finalStates = aut.finalStates;
    T.stateNum = aut.stateNum;
    T.qubitNum = aut.qubitNum;
    T.vars = aut.vars;
    T.constraints = aut.constraints;
    T.hasLoop = aut.hasLoop;
    T.isTopdownDeterministic = aut.isTopdownDeterministic;
    T.transitions = {};
    T.symbolicvarsNum = 0;
    for(auto& transition : aut.transitions){
        if(transition.first.is_internal()){
            AUTOQ::Symbol::Symbolic symbol = transition.first.symbol().qubit();
            AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
            T.transitions[tag] = transition.second;
        }
        if(transition.first.is_leaf()){
            for(const auto& out : transition.second){
                Symbol q = transition.first.symbol();
                auto res = alpha.find(q);
                if(res == alpha.end()){
                    // create new symbolic state
                    AUTOQ::Complex::SymbolicComplex c = AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor("symbolic_" + std::to_string(++T.symbolicvarsNum));
                    AUTOQ::Symbol::Symbolic symbol = AUTOQ::Symbol::Symbolic(c);
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
                    T.transitions[tag][out.first] = out.second;
                    alpha[q] = symbol;
                    inverse_alpha[symbol] = q;
                } else {
                    // use existing symbolic variable
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({res->second, transition.first.tag()});
                    T.transitions[tag][out.first] = out.second;
                }
            }
        }
    }
    return T;
}


template<typename Symbol>
AUTOQ::Symbol::Symbolic eval_mapping(   const AUTOQ::Symbol::Symbolic& symbol_before,
                                        const AUTOQ::Symbol::Symbolic& symbol_after,
                                        InverseAbstractionMap<Symbol>& inverse_alpha,
                                        SymbolicMap& tau,
                                        int& symbolicvarsNum,
                                        bool& changes_behavior,
                                        SymbolicMap& sigma){
    auto res = tau.find(symbol_before);
    if(res == tau.end()){
        tau.insert({symbol_before, symbol_after});
        return symbol_before;
    }
    else{
        if(res->second != symbol_after){
            auto res2 = sigma.find(res->first);
            if(res2 == sigma.end()){
                auto new_symbol = AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor("symbolic_" + std::to_string(++symbolicvarsNum));
                sigma.insert({res->first, new_symbol});
                // add the new symbolic variable to the inverse alpha map
                inverse_alpha[AUTOQ::Symbol::Symbolic(new_symbol)] = inverse_alpha[res->first];
                changes_behavior = true;
                return new_symbol;
            }
            else{
                return res2->second;
            }
        }
        else{
            return res->first;
        }
    }
    return symbol_before;
}

template<typename Symbol>
AUTOQ::Automata<AUTOQ::Symbol::Symbolic> refinement(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& T,
                                                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref,
                                                    SymbolicMap& tau, InverseAbstractionMap<Symbol>& inverse_alpha,
                                                    bool& changes_behavior){

    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> product;
    product.qubitNum = T.qubitNum;
    product.vars = T.vars;
    product.constraints = T.constraints;
    product.hasLoop = T.hasLoop;
    product.isTopdownDeterministic = T.isTopdownDeterministic;
    product.transitions = {};
    product.symbolicvarsNum = Tref.symbolicvarsNum;

    // translate the transition function to
    // Q ---> Color ---> Qubit/Symbol, StateVector
    using ProductPair = std::pair<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::StateVector, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::Symbol>;
    using TransitionsProd = std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State,
                                    std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::Tag, ProductPair>>;

    // {lhs_state, rhs_state} ---> prod_state
    using ProductMap = std::map<std::pair<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State>,
                                AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State>;
    using WorkList = std::deque<std::pair<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State>>;
    WorkList worklist{};
    TransitionsProd lhs;
    TransitionsProd rhs;
    ProductMap mapping;
    for(auto& t1 : T.transitions){
        auto color_set = t1.first.tag();
        for(auto& out : t1.second){
            if(t1.first.is_internal()){
                long int qubit = static_cast<long int>(t1.first.symbol().qubit());
                ProductPair tmp = {*(out.second.begin()), qubit};
                rhs[out.first][color_set] = tmp;
            }
            if(t1.first.is_leaf()){
                auto symbol = t1.first.symbol();
                ProductPair tmp = {*(out.second.begin()), symbol};
                rhs[out.first][color_set] = tmp;
            }
        }
    }
    for(auto& t2 : Tref.transitions){
        auto color_set = t2.first.tag();
        for(auto& out : t2.second){
            if(t2.first.is_internal()){
                long int qubit = static_cast<long int>(t2.first.symbol().qubit());
                ProductPair tmp = {*(out.second.begin()), qubit};
                lhs[out.first][color_set] = tmp;
            }
            if(t2.first.is_leaf()){
                auto symbol = t2.first.symbol();
                ProductPair tmp = {*(out.second.begin()), symbol};
                lhs[out.first][color_set] = tmp;
            }
        }
    }


    // Pair the i-th root before the body with the i-th root after it. Pairing
    // every root with every other root squares the root count each round, so a
    // precondition with more than one state never reaches a fixpoint (#66).
    if (T.finalStates.size() != Tref.finalStates.size())
        THROW_AUTOQ_ERROR("Loop summarization found "
            + std::to_string(Tref.finalStates.size()) + " roots before the loop body and "
            + std::to_string(T.finalStates.size()) + " after it.");
    int64_t state_counter = 0;
    for (size_t i = 0; i < T.finalStates.size(); ++i) {
        auto pair = std::make_pair(Tref.finalStates[i], T.finalStates[i]);
        auto res = mapping.find(pair);
        if (res == mapping.end()) {
            worklist.push_back(pair);
            product.finalStates.emplace_back(state_counter);
            mapping[pair] = state_counter;
            state_counter++;
        }
    }

    SymbolicMap sigma{};
    while(!worklist.empty()){
        auto W = worklist.front();
        worklist.pop_front();
        auto map_lhs = lhs[W.first];
        auto map_rhs = rhs[W.second];
        // Color ---> {StateVector, Qubit/Symbol}
        for(const auto& color : map_lhs){
            auto find_color = map_rhs.find(color.first);
            if(find_color != map_rhs.end()){
                auto qubit_sym_lhs = color.second.second;
                auto qubit_sym_rhs = find_color->second.second;
                if(qubit_sym_lhs.is_internal() && qubit_sym_rhs.is_internal()){
                    if(qubit_sym_lhs != qubit_sym_rhs){
                        THROW_AUTOQ_ERROR("Product construction failure");
                    }
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::StateVector prod_state_vector;
                    for(long unsigned int i = 0; i < color.second.first.size(); i++){
                        auto state_lhs = color.second.first[i];
                        auto state_rhs = find_color->second.first[i];
                        auto statepair = std::make_pair(state_lhs, state_rhs);
                        auto res = mapping.find(statepair);
                        if(res == mapping.end()){
                            worklist.push_back(statepair);
                            mapping[statepair] = state_counter++;
                        }
                        prod_state_vector.push_back(mapping[statepair]);
                    }
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag symboltag = {qubit_sym_lhs, color.first};
                    product.transitions[symboltag][mapping[W]] = {prod_state_vector};
                }
                else if(qubit_sym_lhs.is_leaf() && qubit_sym_rhs.is_leaf()){
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag symboltag = {
                        eval_mapping(qubit_sym_lhs, qubit_sym_rhs, inverse_alpha, tau, product.symbolicvarsNum, changes_behavior, sigma), color.first};

                    product.transitions[symboltag][mapping[W]] = {color.second.first};
                }
                else{
                    THROW_AUTOQ_ERROR("Product construction failure");
                }
            }
        }
    }
    product.stateNum = state_counter;
    return product;
}

template<typename Symbol>
Symbol eval_symbol( const AUTOQ::Symbol::Symbolic& symbol,
                    SymbolicMap& tau,
                    InverseAbstractionMap<Symbol>& symbolmap){
    // A variable v is stored as vR + i·vI. imag() returns the real coefficient
    // of the imaginary part, so substituting vR -> real(v) and vI -> imag(v)
    // rebuilds v. The same substitution works for a number and for an expression (#23).
    using Value = std::decay_t<decltype(std::declval<Symbol>().complex.real())>;
    std::map<AUTOQ::Complex::Term, Value> mapping;
    for(auto& [sym, conc] : symbolmap){
        for(auto& [term, complex] : sym.complex){
            for(auto& [string, cppint] : term){
                if(string.back() == 'I')
                    mapping[term] = conc.complex.imag();
                else if(string.back() == 'R')
                    mapping[term] = conc.complex.real();
                else
                    mapping[term] = Value();
            }
        }
    }
    AUTOQ::Symbol::Symbolic expression = tau[symbol];
    Value sum{};
    for(auto& [term, complex] : expression.complex){
        sum = sum + scale_by_coefficient(complex, mapping[term]);
    }
    return Symbol(sum);
}



template<typename Symbol>
AUTOQ::Automata<Symbol> post_process_sumarization(  AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref,
                                                    InverseAbstractionMap<Symbol>& inverse_alpha,
                                                    SymbolicMap& tau,
                                                    int num_of_iterations){
    AUTOQ::Automata<Symbol> result;
    InverseAbstractionMap<Symbol> alpha = inverse_alpha;
    InverseAbstractionMap<Symbol> new_map = alpha;

    for(int i = 0; i < num_of_iterations; i++){
        for(auto& [symbolic, concrete] : alpha){
            new_map[symbolic] = eval_symbol(symbolic, tau, alpha);
        }
        //swap maps
        std::swap(alpha, new_map);
    }
    inverse_alpha = alpha;

    result.name = Tref.name + "_summarized";
    result.finalStates = Tref.finalStates;
    result.stateNum = Tref.stateNum;
    result.qubitNum = Tref.qubitNum;
    result.vars = Tref.vars;
    result.constraints = Tref.constraints;
    result.hasLoop = Tref.hasLoop;
    result.isTopdownDeterministic = Tref.isTopdownDeterministic;
    result.transitions = {};
    result.symbolicvarsNum = 0;
    for(auto& transition : Tref.transitions){
        if(transition.first.is_internal()){
            Symbol symbol = transition.first.symbol().qubit();
            result.transitions[{symbol, transition.first.tag()}] = transition.second;
        }
        if(transition.first.is_leaf()){
            for(const auto& out : transition.second){
                Symbol symbol = inverse_alpha[transition.first.symbol()];
                result.transitions[{symbol, transition.first.tag()}][out.first] = out.second;
            }
        }
    }

    return result;
}


template<typename Symbol>
AUTOQ::Automata<Symbol> symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, const AUTOQ::QasmRegexes& re, int num_of_iterations, const std::vector<int>& qubit_permutation){
    InverseAbstractionMap<Symbol> inverse_alpha;
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T = initial_abstraction<Symbol>(aut, inverse_alpha);
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> Tref = T;
    SymbolicMap tau{};
    // Fix-point rounds must not add to the program's gate count. Each round
    // assigns a freshly built automaton, which would otherwise point at the
    // global stats object.
    AUTOQ::ExecutionStats abstraction_stats;
    abstraction_stats.gateLog = aut.stats_->gateLog;
    abstraction_stats.opLog = aut.stats_->opLog;
    auto use_abstraction_stats = [&](AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& automaton) {
        automaton.set_execution_stats(&abstraction_stats);
    };
    use_abstraction_stats(T);
    use_abstraction_stats(Tref);
    int gates_per_body = 0;
    // start of main summarization loop
    bool changes_behavior = false;
    do {
        changes_behavior = false;
        T = Tref;
        use_abstraction_stats(T);
        const int before = abstraction_stats.gateCount;
        //execute gates
        for(const std::string& line : loop_body){
            T.single_gate_execute(line, re, qubit_permutation);
        }
        gates_per_body = abstraction_stats.gateCount - before;
        tau.clear();

        // refinement after executing loop body
        Tref = refinement(T, Tref, tau, inverse_alpha, changes_behavior);
        use_abstraction_stats(Tref);

    } while(changes_behavior); // found fix-point
    // One execution of the body, repeated num_of_iterations times. The rounds
    // above only discover the summary.
    if (num_of_iterations > 0)
        aut.stats_->gateCount += gates_per_body * num_of_iterations;
    // post process the summarization result
    AUTOQ::Automata<Symbol> result = post_process_sumarization<Symbol>(Tref, inverse_alpha, tau, num_of_iterations);
    result.share_execution_stats(aut.stats_);
    return result;
}


// https://bytefreaks.net/programming-2/c/c-undefined-reference-to-templated-class-function
template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template void execute_loop<AUTOQ::Symbol::Concrete>(std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, ParameterMap&, const AUTOQ::QasmRegexes&, std::smatch, const std::vector<int>&);
template void execute_loop<AUTOQ::Symbol::Symbolic>(std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, ParameterMap&, const AUTOQ::QasmRegexes&, std::smatch, const std::vector<int>&);