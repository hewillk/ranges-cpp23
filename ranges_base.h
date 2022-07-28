#pragma once

#include <algorithm>
#include <functional>
#include <ranges>
#include <variant>

namespace std::ranges {

template<class V>
concept simple_view = __detail::__simple_view<V>;

template<class T>
concept can_reference = std::__detail::__can_reference<T>;

template<bool Const, class T>
using maybe_const = __detail::__maybe_const_t<Const, T>;

template<bool Const, class V>
using maybe_const_value_t = range_value_t<maybe_const<Const, V>>;

template<bool Const, class V>
using maybe_const_difference_t = range_difference_t<maybe_const<Const, V>>;

template<bool Const, class V>
using maybe_const_reference_t = range_reference_t<maybe_const<Const, V>>;

template<bool Const, class V>
using maybe_const_rvalue_reference_t = range_rvalue_reference_t<maybe_const<Const, V>>;

template<bool Const, class V>
using maybe_const_iterator_t = iterator_t<maybe_const<Const, V>>;

template<bool Const, class V>
using maybe_const_sentinel_t = sentinel_t<maybe_const<Const, V>>;

template<class... Ts>
struct tuple_or_pair_impl : std::type_identity<tuple<Ts...>> { };

template<class T, class U>
struct tuple_or_pair_impl<T, U> : std::type_identity<pair<T, U>> { };

template<class... Ts>
using tuple_or_pair = tuple_or_pair_impl<Ts...>::type;

template<bool Const, class... Views>
using iter_tuple_or_pair = tuple_or_pair<maybe_const_iterator_t<Const, Views>...>;

template<bool Const, class... Views>
constexpr bool iter_tuple_swap_noexcept = noexcept([]<size_t... Is>(index_sequence<Is...>) {
  return (
    noexcept(ranges::iter_swap(get<Is>(declval<const iter_tuple_or_pair<Const, Views...>&>()),
                               get<Is>(declval<const iter_tuple_or_pair<Const, Views...>&>()))) &&
    ...);
}(index_sequence_for<Views...>{}));

template<bool Const, class... Views>
concept iter_tuple_swappable = (indirectly_swappable<maybe_const_iterator_t<Const, Views>> && ...);

template<class... Rs>
concept zip_is_common = (sizeof...(Rs) == 1 && (common_range<Rs> && ...)) ||
  (!(bidirectional_range<Rs> && ...) && (common_range<Rs> && ...)) ||
  ((random_access_range<Rs> && ...) && (sized_range<Rs> && ...));

template<class F, class Tuple>
constexpr auto
tuple_transform(F&& f, Tuple&& tuple) {
  return apply(
    [&]<class... Ts>(Ts&&... elements) {
      return tuple_or_pair<invoke_result_t<F&, Ts>...>(invoke(f, std::forward<Ts>(elements))...);
    },
    std::forward<Tuple>(tuple));
}

template<class F, class Tuple>
constexpr void
tuple_for_each(F&& f, Tuple&& tuple) {
  apply([&]<class... Ts>(Ts&&... elements) { (invoke(f, std::forward<Ts>(elements)), ...); },
        std::forward<Tuple>(tuple));
}

template<size_t N>
constexpr auto
zip_transform_fold(auto transform, auto fold, const auto& x, const auto& y) {
  return [&]<size_t... Is>(index_sequence<Is...>) {
    return fold(transform(get<Is>(x), get<Is>(y))...);
  }
  (make_index_sequence<N>{});
}

template<bool Const, class... Views>
concept all_random_access = (random_access_range<maybe_const<Const, Views>> && ...);

template<bool Const, class... Views>
concept all_bidirectional = (bidirectional_range<maybe_const<Const, Views>> && ...);

template<bool Const, class... Views>
concept all_forward = (forward_range<maybe_const<Const, Views>> && ...);

template<class Cat, class... Iters>
concept all_derived_from = (derived_from<typename iterator_traits<Iters>::iterator_category, Cat> &&
                            ...);

template<class U, size_t>
using same_type = U;

template<class T, class Seq>
struct repeat_tuple_impl;

template<class T, size_t... Is>
struct repeat_tuple_impl<T, index_sequence<Is...>>
  : std::type_identity<tuple_or_pair<same_type<T, Is>...>> { };

template<class T, size_t N>
using repeat_tuple = repeat_tuple_impl<T, make_index_sequence<N>>::type;

template<class F, class T, size_t N>
concept repeat_regular_invocable = []<size_t... Is>(index_sequence<Is...>) {
  return regular_invocable<F, same_type<T, Is>...>;
}
(make_index_sequence<N>{});

template<class F, class T, size_t... Is>
auto repeat_invoke_result_impl(index_sequence<Is...>) -> invoke_result_t<F, same_type<T, Is>...>;

template<class F, class T, size_t N>
using repeat_invoke_result_t = decltype(repeat_invoke_result_impl<F, T>(make_index_sequence<N>{}));

template<class R, class P>
concept compatible_joinable_ranges = common_with<range_value_t<R>, range_value_t<P>> &&
  common_reference_with<range_reference_t<R>, range_reference_t<P>> &&
  common_reference_with<range_rvalue_reference_t<R>, range_rvalue_reference_t<P>>;

template<class R>
concept bidirectional_common = bidirectional_range<R> && common_range<R>;

template<class I>
constexpr I
div_ceil(I num, I denom) {
  I r = num / denom;
  if (num % denom)
    ++r;
  return r;
}

template<class V>
concept slide_caches_nothing = random_access_range<V> && sized_range<V>;

template<class V>
concept slide_caches_last = !slide_caches_nothing<V> && bidirectional_range<V> && common_range<V>;

template<class V>
concept slide_caches_first = !slide_caches_nothing<V> && !slide_caches_last<V>;

template<class First, class... Views>
concept cartesian_is_random_access = (random_access_range<First> && ... &&
                                      (random_access_range<Views> && sized_range<Views>));
template<class R>
concept cartesian_common_arg = common_range<R> ||((random_access_range<R> && sized_range<R>));

template<class First, class... Views>
concept cartesian_is_bidirectional = (bidirectional_range<First> && ... &&
                                      (bidirectional_range<Views> && cartesian_common_arg<Views>));

template<class... Views>
concept cartesian_is_sized = (sized_range<Views> && ...);

template<class First, class... Views>
concept cartesian_sentinel_is_sized = sized_sentinel_for<sentinel_t<First>, iterator_t<First>> &&
  (...&& sized_range<Views>);

template<cartesian_common_arg R>
constexpr auto
cartesian_common_arg_end(R& r) {
  if constexpr (common_range<R>)
    return ranges::end(r);
  else
    return ranges::begin(r) + ranges::size(r);
}

template<class Container>
constexpr bool reservable_container = sized_range<Container>&& requires(Container& c,
                                                                        range_size_t<Container> n) {
  c.reserve(n);
  { c.capacity() } -> same_as<decltype(n)>;
  { c.max_size() } -> same_as<decltype(n)>;
};

template<class Container, class Ref>
constexpr bool container_insertable = requires(Container& c, Ref&& ref) {
  requires(
    requires { c.push_back(std::forward<Ref>(ref)); } ||
    requires { c.insert(c.end(), std::forward<Ref>(ref)); });
};

template<class Ref, class Container>
constexpr auto
container_inserter(Container& c) {
  if constexpr (requires { c.push_back(declval<Ref>()); })
    return back_inserter(c);
  else
    return inserter(c, c.end());
}

}  // namespace std::ranges