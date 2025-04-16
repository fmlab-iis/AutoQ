#include "autoq/loop_sumarization.hh"
#include "autoq/aut_description.hh"
#include "autoq/util/string.hh"
#include <queue>

template<typename Symbol>
void execute_loop(std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, ParameterMap& params, 
                const AUTOQ::regexes& regexes, const std::sregex_iterator& END, std::smatch match_pieces){
    
    int start = std::stoi(match_pieces[2].str());
    int end = std::stoi(match_pieces[3].str());
    int num_of_iterations = end - start + 1;
    if(params["loop"] == "manual"){
        for(int i = start; i <= end; i++){
            for(const std::string& line : loop_body){
                aut.single_gate_execute(line, regexes, END);
            }
        }
        return;
    }
    if(params["loop"] == "symbolic"){
        aut = symbolic_loop<Symbol>(loop_body, aut, regexes, num_of_iterations);
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
    T.vars = aut.vars; // ?
    T.constraints = aut.constraints; // ?
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
                std::cout << "symbolic variable: " << q << std::endl;
                auto res = alpha.find(q);
                if(res == alpha.end()){
                    // create new symbolic state
                    AUTOQ::Complex::SymbolicComplex c = AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor("symbolic_" + std::to_string(++T.symbolicvarsNum));
                    AUTOQ::Symbol::Symbolic symbol = AUTOQ::Symbol::Symbolic(c);
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag tag({symbol, transition.first.tag()});
                    T.transitions[tag][out.first] = out.second;
                    alpha[q] = symbol;
                    inverse_alpha[symbol] = q;
                    std::cout << "new symbolic variable: " << q << "->" << symbol << std::endl;
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
AUTOQ::Symbol::Symbolic eval_mapping(const AUTOQ::Symbol::Symbolic& symbol_before, const AUTOQ::Symbol::Symbolic& symbol_after, 
                                    InverseAbstractionMap<Symbol>& inverse_alpha, SymbolicMap& tau, int& symbolicvarsNum, bool& changes_behavior,
                                    SymbolicMap& sigma){
    auto res = tau.find(symbol_before);
    if(res == tau.end()){
        tau.insert({symbol_before, symbol_after});
        std::cout << "Normal mapping: " << symbol_before << " -> " << symbol_after << std::endl;
        return symbol_before;
    }
    else{
        if(res->second != symbol_after){
            auto res2 = sigma.find(res->first);
            if(res2 == sigma.end()){
                auto new_symbol = AUTOQ::Complex::SymbolicComplex::MySymbolicComplexConstructor("symbolic_" + std::to_string(++symbolicvarsNum));
                sigma.insert({res->first, new_symbol});
                std::cout << "new symbolic variable: " << res->first << "->" << new_symbol << std::endl;
                std::cout << "conflict: " << res->second << "!=" << symbol_after << std::endl;

                // add the new symbolic variable to the inverse alpha map

                inverse_alpha[AUTOQ::Symbol::Symbolic(new_symbol)] = inverse_alpha[res->first];
                std::cout << "new symbolic variable: " << new_symbol << "->" << inverse_alpha[res->first] << std::endl;
                changes_behavior = true;
                return new_symbol;
            }
            else{
                std::cout << "conflict but already new symbolic variable: " << res->first << "->" << res2->second << std::endl;
                return res2->second;
            }
        }
        else{
            std::cout << "already in but no conflict: " << res->first << "->" << res->second << std::endl;
            return res->first;
        }
    }
    return symbol_before;
}

template<typename Symbol>
AUTOQ::Automata<AUTOQ::Symbol::Symbolic> refinement(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& T, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref, 
                                                    SymbolicMap& tau, InverseAbstractionMap<Symbol>& inverse_alpha, bool& changes_behavior){
    // create automata product synchronized by colors
    // a transition is created if Colors1 & Colors2 != 0 (meaning the intersection of colors is not empty)
    // for leaf transitions, eval_mapping() is used to evaluate the symbolic variable in SymbolTag
    std::cout << "Tref:" << std::endl;
    Tref.print_aut();
    std::cout << "T:" << std::endl;
    T.print_aut();



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
    using TransitionsProd = std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, std::map<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::Tag, ProductPair>>;

    // {lhs_state, rhs_state} ---> prod_state
    using ProductMap = std::map<std::pair<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State>, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State>;
    using WorkList = std::deque<std::pair<AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::State>>;
    WorkList worklist{};
    TransitionsProd lhs;
    TransitionsProd rhs;
    ProductMap mapping;
    for(auto& t1 : T.transitions){
        auto color_set = t1.first.tag();
        int index = 1;
        while(color_set > 0){
            if(color_set & 1){
                for(auto& out : t1.second){
                    if(t1.first.is_internal()){
                        long int qubit = static_cast<long int>(t1.first.symbol().qubit());
                        ProductPair tmp = {*(out.second.begin()), qubit};
                        rhs[out.first][index] = tmp;
                    }
                    if(t1.first.is_leaf()){
                        auto symbol = t1.first.symbol();
                        ProductPair tmp = {*(out.second.begin()), symbol};
                        rhs[out.first][index] = tmp;
                    }
                }
            }
            color_set >>= 1;
            index++;
        }
    }
    for(auto& t2 : Tref.transitions){
        auto color_set = t2.first.tag();
        int index = 1;
        while(color_set > 0){
            if(color_set & 1){
                for(auto& out : t2.second){
                    if(t2.first.is_internal()){
                        long int qubit = static_cast<long int>(t2.first.symbol().qubit());
                        ProductPair tmp = {*(out.second.begin()), qubit};
                        lhs[out.first][index] = tmp;
                    }
                    if(t2.first.is_leaf()){
                        auto symbol = t2.first.symbol();
                        ProductPair tmp = {*(out.second.begin()), symbol};
                        lhs[out.first][index] = tmp;
                    }
                }
            }
            color_set >>= 1;
            index++;
        }
    }
    

    // add all initial states to corresponding maps
    int64_t state_counter = 0;
    for(auto& rhs_roots : T.finalStates){
        for(auto& lhs_roots : Tref.finalStates){
            auto pair = std::make_pair(lhs_roots, rhs_roots);
            auto res = mapping.find(pair);
            if(res == mapping.end()){
                std::cout << "pair: " << pair.first << ", " << pair.second << std::endl;
                std::cout << "added initial state: " << state_counter << std::endl;
                worklist.push_back(pair);
                product.finalStates.emplace_back(state_counter);
                mapping[pair] = state_counter;
                state_counter++;
            }
        }
    }

    std::cout << "Worklist after initial adding: ";
    for(auto pair : worklist){
        std::cout << "[" << pair.first << ", " << pair.second << "] ";
    }
    std::cout << std::endl;


    SymbolicMap sigma{};
    while(!worklist.empty()){
        std::cout << "Worklist  status: ";
        for(auto pair : worklist){
            std::cout << "[" << pair.first << ", " << pair.second << "] ";
        }
        std::cout << std::endl;


        auto W = worklist.front();
        worklist.pop_front();
        auto map_lhs = lhs[W.first];
        auto map_rhs = rhs[W.second];
        // Color ---> {Qubit/Symbol, StateVector}
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
                    AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::SymbolTag symboltag = {eval_mapping(qubit_sym_lhs, qubit_sym_rhs, inverse_alpha, tau, product.symbolicvarsNum, changes_behavior, sigma), color.first};
                    product.transitions[symboltag][mapping[W]] = {color.second.first};
                }
                else{
                    THROW_AUTOQ_ERROR("Product construction failure");
                }
            }
        }
    }
    for(auto map : mapping){
        std::cout << "[" << map.first.first << ", " << map.first.second << "] -> " << map.second << std::endl;
    }

    //product.transitions[{level, color}][after_in_prod].insert(prod_state_vector);
    //product.transitions[{eval_mapping(sym_before, sym_after, sigma, tau, T.symbolicvarsNum), intersection}][state_vector] = res->second;
    product.stateNum = state_counter;
    // processing leaf transitions
    // needs colors, parent nodes 
    // the symbol variable is to be evaluated


    product.print_aut();

    return product;
}




// either Symbolic ---> Concrete
// or Symbolic ---> Symbolic (just returns)
template<typename Symbol>
Symbol convert_symbol(const AUTOQ::Symbol::Symbolic& symbol, InverseAbstractionMap<Symbol>& inverse_alpha, SymbolicMap& tau, int num_of_iterations){

    std::cout << "-----------------------------------------------------" << std::endl;

    std::map<AUTOQ::Complex::Term, AUTOQ::Complex::Complex> mapping;
    std::map<AUTOQ::Complex::Term, AUTOQ::Complex::Complex> temp_map;
    for(auto& [sym, conc] : inverse_alpha){
        for(auto& [term, complex] : sym.complex){
            for(auto& [string, cppint] : term){
                std::cout << "Term: " << string << ", " << cppint << ", " << conc << ", " << complex << std::endl;
                if(string.back() == 'I'){
                    mapping[term] = conc.complex;
                    std::cout << "\timaginary part" <<  mapping[term] << std::endl;
                    //mapping[term] = AUTOQ::Complex::Complex(0);
                }
                else if(string.back() == 'R'){
                    mapping[term] = conc.complex;
                    std::cout << "\treal part" <<  mapping[term] << std::endl;
                    //mapping[term] = conc.complex;
                }
                else{
                    mapping[term] = AUTOQ::Complex::Complex(0);
                    std::cout << "\tunknown part" <<  mapping[term] << std::endl;
                }
            }
        }
    }
    std::map<AUTOQ::Complex::Term, AUTOQ::Complex::Complex> new_map = mapping;


    if constexpr (std::is_same_v<Symbol, AUTOQ::Symbol::Concrete>){
        AUTOQ::Symbol::Symbolic expression = tau[symbol];
        // first set cummulative sum to the value of sym (tau = sym -> expr)
        // and multiplied by the value in expr
        /*std::cout << "Expression: " << expression << std::endl;
        for(int i = 0; i < num_of_iterations; i++){
            AUTOQ::Complex::Complex sum(0);
            for(auto& [term, complex] : expression.complex){
                std::cout << "Term: " << term << ", " << complex << std::endl;
                std::cout << complex << " * " << mapping[term] << std::endl;
                AUTOQ::Complex::Complex value = complex * mapping[term];
                std::cout << sum << " + " << value << std::endl;
                sum = sum + value;
            }
            //rewrite in mapping for next iteration
            for(auto& [term, complex] : symbol.complex){
                for(auto& [string, cppint] : term){
                    if(string.back() == 'I'){
                        new_map[term] = sum;
                    }
                    else if(string.back() == 'R'){
                        new_map[term] = sum;
                    }
                    else{
                        new_map[term] = AUTOQ::Complex::Complex(0);
                    }
                }
            }
            // swap the maps
            temp_map = mapping;
            mapping = new_map;
            new_map = temp_map;
        }
        AUTOQ::Complex::Complex sum(0);
        // extract from mapping final values
        for(auto& [term, complex] : symbol.complex){
            sum = sum + mapping[term];
            std::cout << "Term: " << term << ", " << complex << " Sum = " << sum << std::endl;
        }
        return AUTOQ::Symbol::Concrete(sum);*/
    }
    else if(std::is_same_v<Symbol, AUTOQ::Symbol::Symbolic>){
        return symbol;
    }
    THROW_AUTOQ_ERROR("Symbol type conversion not supported");
}



template<typename Symbol>
AUTOQ::Automata<Symbol> post_process_sumarization(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>& Tref, InverseAbstractionMap<Symbol>& inverse_alpha, SymbolicMap& tau, int num_of_iterations){
    AUTOQ::Automata<Symbol> result;
    // todo apply mapping back to values we had before

    for(auto& [symbolic, concrete] : inverse_alpha){
        std::cout << "Symbolic: " << symbolic << std::endl;
        for(auto& [term, complex] : symbolic.complex){
            std::cout << "\tComplex: " << complex << std::endl;
            std::cout << "\tTerms: " << term << std::endl;
        }
        AUTOQ::Complex::SymbolicComplex sym_real = symbolic.complex.real();
        AUTOQ::Complex::SymbolicComplex sym_imag = symbolic.complex.imag();
        std::cout << "Symbolic real part: " << sym_real << std::endl;
        for(auto& [term, complex] : sym_real){
            std::cout << "\tComplex: " << complex << std::endl;
            std::cout << "\tTerms: " << term << std::endl;
        }        
        std::cout << "Symbolic imag part: " << sym_imag << std::endl;
        for(auto& [term, complex] : sym_imag){
            std::cout << "\tComplex: " << complex << std::endl;
            std::cout << "\tTerms: " << term << std::endl;
        }        
    }

    result.name = Tref.name + "_summarized";
    result.finalStates = Tref.finalStates;
    result.stateNum = Tref.stateNum;
    result.qubitNum = Tref.qubitNum;
    result.vars = Tref.vars; // ?
    result.constraints = Tref.constraints; // ?
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
                Symbol symbol = convert_symbol<Symbol>(transition.first.symbol(), inverse_alpha, tau, num_of_iterations);
                result.transitions[{symbol, transition.first.tag()}][out.first] = out.second;
            }
        }
    }

    return result;
}


template<typename Symbol>
AUTOQ::Automata<Symbol> symbolic_loop(const std::vector<std::string>& loop_body, AUTOQ::Automata<Symbol>& aut, const AUTOQ::regexes& regexes, int num_of_iterations){
    InverseAbstractionMap<Symbol> inverse_alpha;
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> T = initial_abstraction<Symbol>(aut, inverse_alpha);
    AUTOQ::Automata<AUTOQ::Symbol::Symbolic> Tref = T;
    SymbolicMap tau{};
    int i = 0;
    // start of main summarization loop
    bool changes_behavior = false;
    do {
        changes_behavior = false;
        std::cout << "Iteration " << ++i << std::endl;
        T.print_aut();
        T = Tref;
        //execute gates
        for(const std::string& line : loop_body){
            T.single_gate_execute(line, regexes, std::sregex_iterator());
        }
        tau.clear();

        // refinement after executing loop body
        Tref = refinement(T, Tref, tau, inverse_alpha, changes_behavior);

        std::cout << "Tau Mapping: " << std::endl;
        for(auto map : tau){
            std::cout << "\t" << map.first << " -> " << map.second << std::endl;
        }
        std::cout << "Inverse alpha Mapping: " << std::endl;
        for(auto map : inverse_alpha){
            std::cout << "\t" << map.first << " -> " << map.second << std::endl;
        }

    } while(changes_behavior); // found fix-point? -- no confliects after the last refinement
    // end of main summarization loop
    
    
    std::cout << "LOOP SUMMARIZED after " << i << " iterations" << std::endl;
    
    std::cout << "Tau Mapping: " << std::endl;
    for(auto map : tau){
        std::cout << "\t" << map.first << " -> " << map.second << std::endl;
    }
    std::cout << "Alpha Mapping: " << std::endl;
    for(auto map : inverse_alpha){
        std::cout << "\t" << map.first << " -> " << map.second << std::endl;
    }

    // post process the summarization result
    AUTOQ::Automata<Symbol> result = post_process_sumarization<Symbol>(Tref, inverse_alpha, tau, num_of_iterations);
    return result;
}



template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;
template void execute_loop<AUTOQ::Symbol::Concrete>(std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template void execute_loop<AUTOQ::Symbol::Symbolic>(std::vector<std::string>&,AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, ParameterMap&, const AUTOQ::regexes&, const std::sregex_iterator&, std::smatch match_pieces);
template AUTOQ::Automata<AUTOQ::Symbol::Concrete> symbolic_loop<AUTOQ::Symbol::Concrete>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, const AUTOQ::regexes&, int);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> symbolic_loop<AUTOQ::Symbol::Symbolic>(const std::vector<std::string>&, AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, const AUTOQ::regexes&, int);
template AUTOQ::Automata<AUTOQ::Symbol::Concrete> post_process_sumarization<AUTOQ::Symbol::Concrete>(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, InverseAbstractionMap<AUTOQ::Symbol::Concrete>&, SymbolicMap&, int);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> post_process_sumarization<AUTOQ::Symbol::Symbolic>(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, InverseAbstractionMap<AUTOQ::Symbol::Symbolic>&, SymbolicMap&, int);
template AUTOQ::Symbol::Concrete convert_symbol<AUTOQ::Symbol::Concrete>(const AUTOQ::Symbol::Symbolic&, InverseAbstractionMap<AUTOQ::Symbol::Concrete>&, SymbolicMap&, int);
template AUTOQ::Symbol::Symbolic convert_symbol<AUTOQ::Symbol::Symbolic>(const AUTOQ::Symbol::Symbolic&, InverseAbstractionMap<AUTOQ::Symbol::Symbolic>&, SymbolicMap&, int);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> initial_abstraction<AUTOQ::Symbol::Concrete>(AUTOQ::Automata<AUTOQ::Symbol::Concrete>&, InverseAbstractionMap<AUTOQ::Symbol::Concrete>&);
template AUTOQ::Automata<AUTOQ::Symbol::Symbolic> initial_abstraction<AUTOQ::Symbol::Symbolic>(AUTOQ::Automata<AUTOQ::Symbol::Symbolic>&, InverseAbstractionMap<AUTOQ::Symbol::Symbolic>&);