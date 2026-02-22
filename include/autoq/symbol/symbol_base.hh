/*****************************************************************************
 *  AUTOQ Tree Automata Library
 *
 *  Description:
 *    CRTP base for symbol types that share internal/leaf and qubit tagging.
 *    Used by Concrete and Symbolic to avoid duplicating is_internal()/is_leaf().
 *
 *****************************************************************************/

#ifndef _AUTOQ_SYMBOL_SYMBOL_BASE_HH_
#define _AUTOQ_SYMBOL_SYMBOL_BASE_HH_

namespace AUTOQ {
namespace Symbol {

/** CRTP base: holds internal/leaf flag and provides is_internal() / is_leaf(). */
template <typename Derived>
struct SymbolBase {
    bool is_internal() const { return internal_; }
    bool is_leaf() const { return !internal_; }

protected:
    bool internal_{false};
    SymbolBase() = default;
    explicit SymbolBase(bool internal) : internal_(internal) {}
};

}  // namespace Symbol
}  // namespace AUTOQ

#endif
