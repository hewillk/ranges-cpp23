#ifndef COMM_REF_HPP
#define COMM_REF_HPP

#include <type_traits>
#include <utility>

template<class X, class Y>
using COND_RES = decltype(false ? std::declval<X(&)()>()() : std::declval<Y(&)()>()());

template<class FROM, class TO>
using COPYCV = std::conditional_t<
  std::is_const_v<FROM>,
  std::conditional_t<std::is_volatile_v<FROM>, std::add_cv_t<TO>, std::add_const_t<TO>>,
  std::conditional_t<std::is_volatile_v<FROM>, std::add_volatile_t<TO>, TO>>;

template<class X, class Y>
using COMMON_REF = COND_RES<COPYCV<X, Y>&, COPYCV<Y, X>&>;

template<class A, class B, class X = std::remove_reference_t<A>,
         class Y = std::remove_reference_t<B>>
  requires std::is_lvalue_reference_v<A> && std::is_lvalue_reference_v<B> &&
           std::is_reference_v<COMMON_REF<X, Y>>
using COMMON_LL = COMMON_REF<X, Y>;

template<class A, class B, class X = std::remove_reference_t<A>,
         class Y = std::remove_reference_t<B>>
  requires std::is_rvalue_reference_v<A> && std::is_rvalue_reference_v<B> &&
           std::is_convertible_v<A, std::remove_reference_t<COMMON_LL<X&, Y&>>&&> &&
           std::is_convertible_v<B, std::remove_reference_t<COMMON_LL<X&, Y&>>&&>
using COMMON_RR = std::remove_reference_t<COMMON_LL<X&, Y&>>&&;

template<class A, class B, class X = std::remove_reference_t<A>,
         class Y = std::remove_reference_t<B>>
  requires std::is_rvalue_reference_v<A> && std::is_lvalue_reference_v<B> &&
           std::is_convertible_v<A, COMMON_LL<const X&, Y&>>
using COMMON_RL = COMMON_LL<const X&, Y&>;

template<class A, class X = std::remove_reference_t<A>>
struct XREF {
  template<class U>
  using T = decltype([] {
    if constexpr (std::is_lvalue_reference_v<A>)
      return std::type_identity<std::add_lvalue_reference_t<COPYCV<X, U>>>{};
    else if constexpr (std::is_rvalue_reference_v<A>)
      return std::type_identity<std::add_rvalue_reference_t<COPYCV<X, U>>>{};
    else
      return std::type_identity<COPYCV<X, U>>{};
  }())::type;
};

template<class T1, class T2>
using BASIC_COMM = typename 
  std::basic_common_reference<std::remove_cvref_t<T1>, std::remove_cvref_t<T2>, 
                              XREF<T1>::template T, XREF<T2>::template T>::type;

template<class...>
struct common_reference;

template<class... Ts>
using common_reference_t = typename common_reference<Ts...>::type;

template<>
struct common_reference<> {};

template<class T>
struct common_reference<T> {
  using type = T;
};

template<class T1, class T2>
struct common_reference<T1, T2> {};

template<class T1, class T2>
  requires requires { requires(
    requires { typename COMMON_LL<T1, T2>; } || 
    requires { typename COMMON_RR<T1, T2>; } ||
    requires { typename COMMON_RL<T1, T2>; } || 
    requires { typename COMMON_RL<T2, T1>; } ||
    requires { typename BASIC_COMM<T1, T2>; } ||
    requires { typename COND_RES<T1, T2>; } || 
    requires { typename std::common_type_t<T1, T2>; });
  }
struct common_reference<T1, T2> {
  using type = decltype([] {
    if constexpr (requires { typename COMMON_LL<T1, T2>; })
      return std::type_identity<COMMON_LL<T1, T2>>{};
    else if constexpr (requires { typename COMMON_RR<T1, T2>; })
      return std::type_identity<COMMON_RR<T1, T2>>{};
    else if constexpr (requires { typename COMMON_RL<T1, T2>; })
      return std::type_identity<COMMON_RL<T1, T2>>{};
    else if constexpr (requires { typename COMMON_RL<T2, T1>; })
      return std::type_identity<COMMON_RL<T2, T1>>{};
    else if constexpr (requires { typename BASIC_COMM<T1, T2>; })
      return std::type_identity<BASIC_COMM<T1, T2>>{};
    else if constexpr (requires { typename COND_RES<T1, T2>; })
      return std::type_identity<COND_RES<T1, T2>>{};
    else
      return std::type_identity<std::common_type_t<T1, T2>>{};
  }())::type;
};

template<class T1, class T2, class T3, class... Rest>
struct common_reference<T1, T2, T3, Rest...> {};

template<class T1, class T2, class T3, class... Rest>
  requires requires { typename common_reference_t<common_reference_t<T1, T2>, T3, Rest...>; }
struct common_reference<T1, T2, T3, Rest...> {
  using type = common_reference_t<common_reference_t<T1, T2>, T3, Rest...>;
};

#endif