#ifndef RANGES_CPP23_HPP
#define RANGES_CPP23_HPP

#include <algorithm>
#include <functional>
#include <ranges>
#include <variant>

namespace std::ranges {

template<class V>
concept simple_view = __detail::__simple_view<V>;

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

template<input_range... Views>
  requires((view<Views> && ...) && (sizeof...(Views) > 0))
class zip_view : public view_interface<zip_view<Views...>> {
  template<copy_constructible F, input_range... Uiews>
    requires((view<Uiews> && ...) && (sizeof...(Uiews) > 0) && is_object_v<F> &&
             regular_invocable<F&, range_reference_t<Uiews>...> &&
             std::__detail::__can_reference<invoke_result_t<F&, range_reference_t<Uiews>...>>)
  friend class zip_transform_view;

  tuple<Views...> views_;

  template<bool>
  class sentinel;

  template<bool>
  struct zip_view_iter_cat { };

  template<bool Const>
    requires all_forward<Const, Views...>
  struct zip_view_iter_cat<Const> {
    using iterator_category = input_iterator_tag;
  };

  template<bool Const>
  class iterator : public zip_view_iter_cat<Const> {
    using iter_tuple = iter_tuple_or_pair<Const, Views...>;
    iter_tuple current_;

    constexpr explicit iterator(iter_tuple current) : current_(std::move(current)) { }

    friend zip_view;
    template<bool>
    friend class sentinel;

   public:
    using iterator_concept = decltype([] {
      if constexpr (all_random_access<Const, Views...>)
        return random_access_iterator_tag{};
      else if constexpr (all_bidirectional<Const, Views...>)
        return bidirectional_iterator_tag{};
      else if constexpr (all_forward<Const, Views...>)
        return forward_iterator_tag{};
      else
        return input_iterator_tag{};
    }());
    using value_type = tuple_or_pair<maybe_const_value_t<Const, Views>...>;
    using difference_type = common_type_t<maybe_const_difference_t<Const, Views>...>;

    iterator() = default;

    constexpr iterator(iterator<!Const> i) requires Const &&
      ((convertible_to<iterator_t<Views>, maybe_const_iterator_t<Const, Views>> && ...))
      : current_(std::move(i.current_)) { }

    constexpr auto
    operator*() const {
      return tuple_transform([](auto& i) -> decltype(auto) { return *i; }, current_);
    }

    constexpr iterator&
    operator++() {
      tuple_for_each([](auto& i) { ++i; }, current_);
      return *this;
    }

    constexpr void
    operator++(int) {
      ++*this;
    }

    constexpr iterator
    operator++(int) requires all_forward<Const, Views...> {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires all_bidirectional<Const, Views...> {
      tuple_for_each([](auto& i) { --i; }, current_);
      return *this;
    }

    constexpr iterator
    operator--(int) requires all_bidirectional<Const, Views...> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type n) requires all_random_access<Const, Views...> {
      tuple_for_each([&]<class I>(I& i) { i += iter_difference_t<I>(n); }, current_);
      return *this;
    }

    constexpr iterator&
    operator-=(difference_type n) requires all_random_access<Const, Views...> {
      tuple_for_each([&]<class I>(I& i) { i -= iter_difference_t<I>(n); }, current_);
      return *this;
    }

    constexpr auto
    operator[](difference_type n) const requires all_random_access<Const, Views...> {
      return tuple_transform(
        [&]<class I>(I& i) -> decltype(auto) { return i[iter_difference_t<I>(n)]; }, current_);
    }

    friend constexpr bool
    operator==(const iterator& x, const iterator& y) requires(
      (equality_comparable<maybe_const_iterator_t<Const, Views>> && ...)) {
      if constexpr (all_bidirectional<Const, Views...>)
        return x.current_ == y.current_;
      else
        return zip_transform_fold<sizeof...(Views)>(
          [](const auto& x, const auto& y) { return bool(x == y); },
          [](auto... equals) { return (equals || ...); }, x.current_, y.current_);
    }

    friend constexpr auto
    operator<=>(const iterator& x, const iterator& y) requires all_random_access<Const, Views...> {
      return x.current_ <=> y.current_;
    }

    friend constexpr iterator
    operator+(const iterator& i, difference_type n) requires all_random_access<Const, Views...> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator+(difference_type n, const iterator& i) requires all_random_access<Const, Views...> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator-(const iterator& i, difference_type n) requires all_random_access<Const, Views...> {
      auto r = i;
      r -= n;
      return r;
    }

    friend constexpr difference_type
    operator-(const iterator& x, const iterator& y) requires(
      (sized_sentinel_for<maybe_const_iterator_t<Const, Views>,
                          maybe_const_iterator_t<Const, Views>> &&
       ...)) {
      return zip_transform_fold<sizeof...(Views)>(
        [](const auto& x, const auto& y) { return difference_type(x - y); },
        [](auto... dists) {
          return ranges::min({dists...}, {}, [](auto dist) { return std::abs(dist); });
        },
        x.current_, y.current_);
    }

    friend constexpr auto
    iter_move(const iterator& i) noexcept(
      (noexcept(ranges::iter_move(declval<const maybe_const_iterator_t<Const, Views>&>())) &&
       ...) &&
      (is_nothrow_move_constructible_v<maybe_const_rvalue_reference_t<Const, Views>> && ...)) {
      return tuple_transform(ranges::iter_move, i.current_);
    }

    friend constexpr void
    iter_swap(const iterator& x, const iterator& y) noexcept(
      iter_tuple_swap_noexcept<Const, Views...>) requires iter_tuple_swappable<Const, Views...> {
      [&]<size_t... Is>(index_sequence<Is...>) {
        (ranges::iter_swap(get<Is>(x.current_), get<Is>(y.current_)), ...);
      }
      (index_sequence_for<Views...>{});
    }
  };

  template<bool Const>
  class sentinel {
    using sentinel_tuple = tuple_or_pair<maybe_const_sentinel_t<Const, Views>...>;

    sentinel_tuple end_;

    constexpr explicit sentinel(sentinel_tuple end) : end_(end) { }

    friend zip_view;

    template<bool OtherConst>
    constexpr auto&
    get_current(const iterator<OtherConst>& iter) const noexcept {
      return zip_view::get_current(iter);
    }

   public:
    sentinel() = default;

    constexpr sentinel(sentinel<!Const> s) requires Const &&
      ((convertible_to<sentinel_t<Views>, maybe_const_sentinel_t<Const, Views>> && ...))
      : end_(std::move(s.end_)) { }

    template<bool OtherConst>
      requires((sentinel_for<maybe_const_sentinel_t<Const, Views>,
                             maybe_const_iterator_t<OtherConst, Views>> &&
                ...))
    friend constexpr bool
    operator==(const iterator<OtherConst>& x, const sentinel& y) {
      return zip_transform_fold<sizeof...(Views)>(
        [](const auto& x, const auto& y) { return bool(x == y); },
        [](auto... equals) { return (equals || ...); }, y.get_current(x), y.end_);
    }

    template<bool OtherConst>
      requires((sized_sentinel_for<maybe_const_sentinel_t<Const, Views>,
                                   maybe_const_iterator_t<OtherConst, Views>> &&
                ...))
    friend constexpr common_type_t<maybe_const_difference_t<OtherConst, Views>...>
    operator-(const iterator<OtherConst>& x, const sentinel& y) {
      using D = common_type_t<maybe_const_difference_t<OtherConst, Views>...>;
      return zip_transform_fold<sizeof...(Views)>(
        [](const auto& x, const auto& y) { return D(x - y); },
        [](auto... dists) {
          return ranges::min({dists...}, {}, [](auto dist) { return std::abs(dist); });
        },
        y.get_current(x), y.end_);
    }

    template<bool OtherConst>
      requires((sized_sentinel_for<maybe_const_sentinel_t<Const, Views>,
                                   maybe_const_iterator_t<OtherConst, Views>> &&
                ...))
    friend constexpr common_type_t<maybe_const_difference_t<OtherConst, Views>...>
    operator-(const sentinel& y, const iterator<OtherConst>& x) {
      return -(x - y);
    }
  };

  template<bool Const>
  static constexpr auto&
  get_current(const iterator<Const>& iter) noexcept {
    return iter.current_;
  }

 public:
  zip_view() = default;

  constexpr explicit zip_view(Views... views) : views_(std::move(views)...) { }

  constexpr auto
  begin() requires(!(simple_view<Views> && ...)) {
    return iterator<false>(tuple_transform(ranges::begin, views_));
  }

  constexpr auto
  begin() const requires((range<const Views> && ...)) {
    return iterator<true>(tuple_transform(ranges::begin, views_));
  }

  constexpr auto
  end() requires(!(simple_view<Views> && ...)) {
    if constexpr (!zip_is_common<Views...>)
      return sentinel<false>(tuple_transform(ranges::end, views_));
    else if constexpr ((random_access_range<Views> && ...))
      return begin() + iter_difference_t<iterator<false>>(size());
    else
      return iterator<false>(tuple_transform(ranges::end, views_));
  }

  constexpr auto
  end() const requires((range<const Views> && ...)) {
    if constexpr (!zip_is_common<const Views...>)
      return sentinel<true>(tuple_transform(ranges::end, views_));
    else if constexpr ((random_access_range<const Views> && ...))
      return begin() + iter_difference_t<iterator<true>>(size());
    else
      return iterator<true>(tuple_transform(ranges::end, views_));
  }

  constexpr auto
  size() requires((sized_range<Views> && ...)) {
    return apply(
      [](auto... sizes) {
        using CT = __detail::__make_unsigned_like_t<common_type_t<decltype(sizes)...>>;
        return ranges::min({CT(sizes)...});
      },
      tuple_transform(ranges::size, views_));
  }

  constexpr auto
  size() const requires((sized_range<const Views> && ...)) {
    return apply(
      [](auto... sizes) {
        using CT = __detail::__make_unsigned_like_t<common_type_t<decltype(sizes)...>>;
        return ranges::min({CT(sizes)...});
      },
      tuple_transform(ranges::size, views_));
  }
};

template<class... Rs>
zip_view(Rs&&...) -> zip_view<views::all_t<Rs>...>;

namespace views {

inline constexpr auto zip = []<viewable_range... Rs>(Rs && ... rs) {
  if constexpr (sizeof...(Rs) == 0)
    return views::empty<tuple<>>;
  else
    return zip_view<all_t<Rs>...>(std::forward<Rs>(rs)...);
};

}  // namespace views

}  // namespace std::ranges

namespace std::ranges {

template<class Cat, class... Iters>
concept all_derived_from = (derived_from<typename iterator_traits<Iters>::iterator_category, Cat> &&
                            ...);

template<copy_constructible F, input_range... Views>
  requires((view<Views> && ...) && (sizeof...(Views) > 0) && is_object_v<F> &&
           regular_invocable<F&, range_reference_t<Views>...> &&
           std::__detail::__can_reference<invoke_result_t<F&, range_reference_t<Views>...>>)
class zip_transform_view : public view_interface<zip_transform_view<F, Views...>> {
  __detail::__box<F> fun_;
  zip_view<Views...> zip_;

  using InnerView = zip_view<Views...>;
  template<bool Const>
  using Base = maybe_const<Const, InnerView>;
  template<bool Const>
  using ziperator = iterator_t<Base<Const>>;
  template<bool Const>
  using zentinel = sentinel_t<Base<Const>>;

  template<bool Const>
  struct zip_transform_iter_cat { };

  template<bool Const>
    requires forward_range<Base<Const>>
  struct zip_transform_iter_cat<Const> {
    using iterator_category = decltype([] {
      if constexpr (!is_lvalue_reference_v<invoke_result_t<
                      maybe_const<Const, F>&, maybe_const_reference_t<Const, Views>...>>)
        return input_iterator_tag{};
      else {
        if constexpr (all_derived_from<random_access_iterator_tag,
                                       maybe_const_iterator_t<Const, Views>...>)
          return random_access_iterator_tag{};
        else if constexpr (all_derived_from<bidirectional_iterator_tag,
                                            maybe_const_iterator_t<Const, Views>...>)
          return bidirectional_iterator_tag{};
        else if constexpr (all_derived_from<forward_iterator_tag,
                                            maybe_const_iterator_t<Const, Views>...>)
          return forward_iterator_tag{};
        else
          return input_iterator_tag{};
      }
    }());
  };

  template<bool Const>
  class iterator : public zip_transform_iter_cat<Const> {
    using Parent = maybe_const<Const, zip_transform_view>;
    using Base = zip_transform_view::Base<Const>;

    Parent* parent_ = nullptr;
    ziperator<Const> inner_;

    constexpr iterator(Parent& parent, ziperator<Const> inner)
      : parent_(addressof(parent)), inner_(std::move(inner)) { }

    friend zip_transform_view;

   public:
    using iterator_concept = ziperator<Const>::iterator_concept;
    using value_type = remove_cvref_t<
      invoke_result_t<maybe_const<Const, F>&, maybe_const_reference_t<Const, Views>...>>;
    using difference_type = range_difference_t<Base>;

    iterator() = default;

    constexpr iterator(iterator<!Const> i) requires Const &&
      (convertible_to<ziperator<false>, ziperator<Const>>)
      : parent_(i.parent_), inner_(std::move(i.inner_)) { }

    constexpr decltype(auto)
    operator*() const noexcept([]<size_t... Is>(index_sequence<Is...>) {
      return noexcept(invoke(*parent_->fun_, *get<Is>(InnerView::get_current(inner_))...));
    }(index_sequence_for<Views...>{})) {
      return apply(
        [&](const auto&... iters) -> decltype(auto) { return invoke(*parent_->fun_, *iters...); },
        InnerView::get_current(inner_));
    }

    constexpr iterator&
    operator++() {
      ++inner_;
      return *this;
    }

    constexpr void
    operator++(int) {
      ++*this;
    }

    constexpr iterator
    operator++(int) requires forward_range<Base> {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires bidirectional_range<Base> {
      --inner_;
      return *this;
    }

    constexpr iterator
    operator--(int) requires bidirectional_range<Base> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type n) requires random_access_range<Base> {
      inner_ += n;
      return *this;
    }

    constexpr iterator&
    operator-=(difference_type n) requires random_access_range<Base> {
      inner_ -= n;
      return *this;
    }

    constexpr decltype(auto)
    operator[](difference_type n) const requires random_access_range<Base> {
      return apply(
        [&]<class... Is>(const Is&... iters) -> decltype(auto) {
          return invoke(*parent_->fun_, iters[iter_difference_t<Is>(n)]...);
        },
        InnerView::get_current(inner_));
    }

    friend constexpr bool
    operator==(const iterator& x,
               const iterator& y) requires equality_comparable<ziperator<Const>> {
      return x.inner_ == y.inner_;
    }

    friend constexpr auto
    operator<=>(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.inner_ <=> y.inner_;
    }

    friend constexpr iterator
    operator+(const iterator& i, difference_type n) requires random_access_range<Base> {
      return iterator(*i.parent_, i.inner_ + n);
    }

    friend constexpr iterator
    operator+(difference_type n, const iterator& i) requires random_access_range<Base> {
      return iterator(*i.parent_, i.inner_ + n);
    }

    friend constexpr iterator
    operator-(const iterator& i, difference_type n) requires random_access_range<Base> {
      return iterator(*i.parent_, i.inner_ - n);
    }

    friend constexpr difference_type
    operator-(const iterator& x,
              const iterator& y) requires sized_sentinel_for<ziperator<Const>, ziperator<Const>> {
      return x.inner_ - y.inner_;
    }
  };

  template<bool Const>
  class sentinel {
    zentinel<Const> inner_;

    constexpr sentinel(zentinel<Const> inner) : inner_(inner) { }

    friend zip_transform_view;

   public:
    sentinel() = default;

    constexpr sentinel(sentinel<!Const> i) requires Const &&
      (convertible_to<zentinel<false>, zentinel<Const>>)
      : inner_(std::move(i.inner_)) { }

    template<bool OtherConst>
      requires sentinel_for<zentinel<Const>, ziperator<OtherConst>>
    friend constexpr bool
    operator==(const iterator<OtherConst>& x, const sentinel& y) {
      return x.inner_ == y.inner_;
    }

    template<bool OtherConst>
      requires sized_sentinel_for<zentinel<Const>, ziperator<OtherConst>>
    friend constexpr maybe_const_difference_t<OtherConst, InnerView>
    operator-(const iterator<OtherConst>& x, const sentinel& y) {
      return x.inner_ - y.inner_;
    }

    template<bool OtherConst>
      requires sized_sentinel_for<zentinel<Const>, ziperator<OtherConst>>
    friend constexpr maybe_const_difference_t<OtherConst, InnerView>
    operator-(const sentinel& x, const iterator<OtherConst>& y) {
      return x.inner_ - y.inner_;
    }
  };

 public:
  zip_transform_view() = default;

  constexpr explicit zip_transform_view(F fun, Views... views)
    : fun_(std::move(fun)), zip_(std::move(views)...) { }

  constexpr auto
  begin() {
    return iterator<false>(*this, zip_.begin());
  }

  constexpr auto
  begin() const requires range<const InnerView> &&
    regular_invocable<const F&, range_reference_t<const Views>...> {
    return iterator<true>(*this, zip_.begin());
  }

  constexpr auto
  end() {
    if constexpr (common_range<InnerView>)
      return iterator<false>(*this, zip_.end());
    else
      return sentinel<false>(zip_.end());
  }

  constexpr auto
  end() const requires range<const InnerView> &&
    regular_invocable<const F&, range_reference_t<const Views>...> {
    if constexpr (common_range<const InnerView>)
      return iterator<true>(*this, zip_.end());
    else
      return sentinel<true>(zip_.end());
  }

  constexpr auto
  size() requires sized_range<InnerView> {
    return zip_.size();
  }

  constexpr auto
  size() const requires sized_range<const InnerView> {
    return zip_.size();
  }
};

template<class F, class... Rs>
zip_transform_view(F, Rs&&...) -> zip_transform_view<F, views::all_t<Rs>...>;

namespace views {

inline constexpr auto zip_transform = []<class F, viewable_range... Rs>(F&& f, Rs&&... rs) {
  if constexpr (sizeof...(Rs) == 0)
    return ((void)std::forward<F>(f), views::empty<decay_t<invoke_result_t<decay_t<F>&>>>);
  else
    return zip_transform_view(std::forward<F>(f), std::forward<Rs>(rs)...);
};

}  // namespace views

}  // namespace std::ranges

namespace std::ranges {

template<class U, size_t>
using same_type = U;

template<class T, class Seq>
struct repeat_tuple_impl;

template<class T, size_t... Is>
struct repeat_tuple_impl<T, index_sequence<Is...>> {
  using type = tuple_or_pair<same_type<T, Is>...>;
};

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

template<forward_range V, size_t N>
  requires((view<V> && N > 0))
class adjacent_view : public view_interface<adjacent_view<V, N>> {
  template<forward_range U, copy_constructible F, size_t M>
    requires(view<U> && (N > 0) && is_object_v<F> &&
             repeat_regular_invocable<F&, range_reference_t<U>, M> &&
             std::__detail::__can_reference<repeat_invoke_result_t<F&, range_reference_t<U>, M>>)
  friend class adjacent_transform_view;

  V base_ = V();

  struct as_sentinel { };

  template<bool Const>
  class iterator {
    using Base = maybe_const<Const, V>;
    array<iterator_t<Base>, N> current_ = array<iterator_t<Base>, N>();

    constexpr iterator(iterator_t<Base> first, sentinel_t<Base> last) {
      current_.front() = std::move(first);
      for (size_t i = 1; i < N; i++)
        current_[i] = ranges::next(current_[i - 1], 1, last);
    }

    constexpr iterator(as_sentinel, iterator_t<Base> first, iterator_t<Base> last) {
      if constexpr (!bidirectional_range<Base>)
        for (auto& i : current_)
          i = last;
      else {
        current_.back() = std::move(last);
        for (size_t i = 1; i < N; i++)
          current_[N - i - 1] = ranges::prev(current_[N - i], 1, first);
      }
    }

    friend adjacent_view;

   public:
    using iterator_category = input_iterator_tag;
    using iterator_concept = conditional_t<
      random_access_range<Base>, random_access_iterator_tag,
      conditional_t<bidirectional_range<Base>, bidirectional_iterator_tag, forward_iterator_tag>>;
    using value_type = repeat_tuple<range_value_t<Base>, N>;
    using difference_type = range_difference_t<Base>;

    iterator() = default;

    constexpr iterator(iterator<!Const> i) requires Const
      && convertible_to<iterator_t<V>, iterator_t<Base>> {
      ranges::move(i.current_, current_.begin());
    }

    constexpr auto
    operator*() const {
      return tuple_transform([](auto& i) -> decltype(auto) { return *i; }, current_);
    }

    constexpr iterator&
    operator++() {
      for (auto& i : current_)
        i = ranges::next(i);
      return *this;
    }

    constexpr iterator
    operator++(int) {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires bidirectional_range<Base> {
      for (auto& i : current_)
        i = ranges::prev(i);
      return *this;
    }

    constexpr iterator
    operator--(int) requires bidirectional_range<Base> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type n) requires random_access_range<Base> {
      for (auto& i : current_)
        i = i + n;
      return *this;
    }

    constexpr iterator&
    operator-=(difference_type n) requires random_access_range<Base> {
      for (auto& i : current_)
        i = i - n;
      return *this;
    }

    constexpr auto
    operator[](difference_type n) const requires random_access_range<Base> {
      return tuple_transform([&](auto& i) -> decltype(auto) { return i[n]; }, current_);
    }

    friend constexpr bool
    operator==(const iterator& x, const iterator& y) {
      return x.current_.back() == y.current_.back();
    }

    friend constexpr bool
    operator<(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.current_.back() < y.current_.back();
    }

    friend constexpr bool
    operator>(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return y < x;
    }

    friend constexpr bool
    operator<=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(y < x);
    }

    friend constexpr bool
    operator>=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(x < y);
    }

    friend constexpr auto
    operator<=>(const iterator& x, const iterator& y) requires random_access_range<Base> &&
      three_way_comparable<iterator_t<Base>> {
      return x.current_.back() <=> y.current_.back();
    }

    friend constexpr iterator
    operator+(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator+(difference_type n, const iterator& i) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator-(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r -= n;
      return r;
    }

    friend constexpr difference_type
    operator-(const iterator& x,
              const iterator& y) requires sized_sentinel_for<iterator_t<Base>, iterator_t<Base>> {
      return x.current_.back() - y.current_.back();
    }

    constexpr auto
    iter_move(const iterator& i) noexcept(
      noexcept(ranges::iter_move(declval<const iterator_t<Base>&>())) &&
      is_nothrow_move_constructible_v<range_rvalue_reference_t<Base>>) {
      return tuple_transform(ranges::iter_move, i.current_);
    }

    constexpr void
    iter_swap(const iterator& x, const iterator& y) noexcept(noexcept(ranges::iter_swap(
      declval<iterator_t<Base>>(),
      declval<iterator_t<Base>>()))) requires indirectly_swappable<iterator_t<Base>> {
      for (size_t i = 0; i < N; i++)
        ranges::swap(x.current_[i], y.current_[i]);
    }
  };

  template<bool Const>
  class sentinel {
    using Base = maybe_const<Const, V>;
    sentinel_t<Base> end_ = sentinel_t<Base>();

    constexpr explicit sentinel(sentinel_t<Base> end) : end_(end) { }

    friend adjacent_view;

   public:
    sentinel() = default;

    constexpr sentinel(sentinel<!Const> s) requires Const &&
      (convertible_to<sentinel_t<V>, sentinel_t<Base>>)
      : end_(std::move(s.end_)) { }

    template<bool OtherConst>
      requires sentinel_for<sentinel_t<Base>, maybe_const_iterator_t<OtherConst, V>>
    friend constexpr bool
    operator==(const iterator<OtherConst>& x, const sentinel& y) {
      return x.current_.back() == y.end_;
    }

    template<bool OtherConst>
      requires sized_sentinel_for<sentinel_t<Base>, maybe_const_iterator_t<OtherConst, V>>
    friend constexpr maybe_const_difference_t<OtherConst, V>
    operator-(const iterator<OtherConst>& x, const sentinel& y) {
      return x.current_.back() - y.end_;
    }

    template<bool OtherConst>
      requires sized_sentinel_for<sentinel_t<Base>, maybe_const_iterator_t<OtherConst, V>>
    friend constexpr maybe_const_difference_t<OtherConst, V>
    operator-(const sentinel& y, const iterator<OtherConst>& x) {
      return y.end_ - x.current_.back();
    }
  };

  template<bool Const>
  static constexpr auto&
  get_current(const iterator<Const>& iter) noexcept {
    return iter.current_;
  }

 public:
  adjacent_view() requires(default_initializable<V>) = default;

  constexpr explicit adjacent_view(V base) : base_(std::move(base)) { }

  constexpr auto
  begin() requires(!simple_view<V>) {
    return iterator<false>(ranges::begin(base_), ranges::end(base_));
  }

  constexpr auto
  begin() const requires range<const V> {
    return iterator<true>(ranges::begin(base_), ranges::end(base_));
  }

  constexpr auto
  end() requires(!simple_view<V>) {
    if constexpr (common_range<V>)
      return iterator<false>(as_sentinel{}, ranges::begin(base_), ranges::end(base_));
    else
      return sentinel<false>(ranges::end(base_));
  }

  constexpr auto
  end() const requires range<const V> {
    if constexpr (common_range<const V>)
      return iterator<true>(as_sentinel{}, ranges::begin(base_), ranges::end(base_));
    else
      return sentinel<true>(ranges::end(base_));
  }

  constexpr auto
  size() requires sized_range<V> {
    using ST = decltype(ranges::size(base_));
    using CT = common_type_t<ST, size_t>;
    auto sz = static_cast<CT>(ranges::size(base_));
    sz -= std::min<CT>(sz, N - 1);
    return static_cast<ST>(sz);
  }

  constexpr auto
  size() const requires sized_range<const V> {
    using ST = decltype(ranges::size(base_));
    using CT = common_type_t<ST, size_t>;
    auto sz = static_cast<CT>(ranges::size(base_));
    sz -= std::min<CT>(sz, N - 1);
    return static_cast<ST>(sz);
  }
};

}  // namespace std::ranges

namespace std::ranges {

template<forward_range V, copy_constructible F, size_t N>
  requires(view<V> && (N > 0) && is_object_v<F> &&
           repeat_regular_invocable<F&, range_reference_t<V>, N> &&
           std::__detail::__can_reference<repeat_invoke_result_t<F&, range_reference_t<V>, N>>)
class adjacent_transform_view : public view_interface<adjacent_transform_view<V, F, N>> {
  __detail::__box<F> fun_;
  adjacent_view<V, N> inner_;

  using InnerView = adjacent_view<V, N>;
  template<bool Const>
  using inner_iterator = iterator_t<maybe_const<Const, InnerView>>;
  template<bool Const>
  using inner_sentinel = sentinel_t<maybe_const<Const, InnerView>>;

  template<bool Const>
  class iterator {
    using Parent = maybe_const<Const, adjacent_transform_view>;
    using Base = maybe_const<Const, V>;

    Parent* parent_ = nullptr;
    inner_iterator<Const> inner_;

    constexpr iterator(Parent& parent, inner_iterator<Const> inner)
      : parent_(addressof(parent)), inner_(std::move(inner)) { }

    friend adjacent_transform_view;

   public:
    using iterator_category = decltype([] {
      if constexpr (!is_lvalue_reference_v<
                      repeat_invoke_result_t<maybe_const<Const, F>&, range_reference_t<Base>, N>>)
        return input_iterator_tag{};
      else {
        using C = iterator_traits<iterator_t<Base>>::iterator_category;
        if constexpr (derived_from<C, random_access_iterator_tag>)
          return random_access_iterator_tag{};
        else if constexpr (derived_from<C, bidirectional_iterator_tag>)
          return bidirectional_iterator_tag{};
        else if constexpr (derived_from<C, forward_iterator_tag>)
          return forward_iterator_tag{};
        else
          return input_iterator_tag{};
      }
    }());
    using iterator_concept = inner_iterator<Const>::iterator_concept;
    using value_type =
      remove_cvref_t<repeat_invoke_result_t<maybe_const<Const, F>&, range_reference_t<Base>, N>>;
    using difference_type = range_difference_t<Base>;

    iterator() = default;

    constexpr iterator(iterator<!Const> i) requires Const
      && convertible_to<inner_iterator<false>, inner_iterator<Const>>
      : parent_(i.parent_), inner_(std::move(i.inner_)) { }

    constexpr decltype(auto)
    operator*() const noexcept([]<size_t... Is>(index_sequence<Is...>) {
      return noexcept(invoke(*parent_->fun_, *get<Is>(InnerView::get_current(inner_))...));
    }(make_index_sequence<N>{})) {
      return apply(
        [&](const auto&... iters) -> decltype(auto) { return invoke(*parent_->fun_, *iters...); },
        InnerView::get_current(inner_));
    }

    constexpr iterator&
    operator++() {
      ++inner_;
      return *this;
    }

    constexpr iterator
    operator++(int) {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires bidirectional_range<Base> {
      --inner_;
      return *this;
    }

    constexpr iterator
    operator--(int) requires bidirectional_range<Base> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type n) requires random_access_range<Base> {
      inner_ += n;
      return *this;
    }

    constexpr iterator&
    operator-=(difference_type n) requires random_access_range<Base> {
      inner_ -= n;
      return *this;
    }

    constexpr decltype(auto)
    operator[](difference_type n) const requires random_access_range<Base> {
      return apply(
        [&](const auto&... iters) -> decltype(auto) { return invoke(*parent_->fun_, iters[n]...); },
        InnerView::get_current(inner_));
    }

    friend constexpr bool
    operator==(const iterator& x, const iterator& y) {
      return x.inner_ == y.inner_;
    }

    friend constexpr bool
    operator<(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.inner_ < y.inner_;
    }

    friend constexpr bool
    operator>(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.inner_ > y.inner_;
    }

    friend constexpr bool
    operator<=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.inner_ <= y.inner_;
    }

    friend constexpr bool
    operator>=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.inner_ >= y.inner_;
    }

    friend constexpr auto
    operator<=>(const iterator& x, const iterator& y) requires random_access_range<Base> &&
      three_way_comparable<inner_iterator<Const>> {
      return x.inner_ <=> y.inner_;
    }

    friend constexpr iterator
    operator+(const iterator& i, difference_type n) requires random_access_range<Base> {
      return iterator(*i.parent_, i.inner_ + n);
    }

    friend constexpr iterator
    operator+(difference_type n, const iterator& i) requires random_access_range<Base> {
      return iterator(*i.parent_, i.inner_ + n);
    }

    friend constexpr iterator
    operator-(const iterator& i, difference_type n) requires random_access_range<Base> {
      return iterator(*i.parent_, i.inner_ - n);
    }

    friend constexpr difference_type
    operator-(const iterator& x, const iterator& y) requires
      sized_sentinel_for<inner_iterator<Const>, inner_iterator<Const>> {
      return x.inner_ - y.inner_;
    }
  };

  template<bool Const>
  class sentinel {
    inner_sentinel<Const> inner_;

    constexpr explicit sentinel(inner_sentinel<Const> inner) : inner_(inner) { }

    friend adjacent_transform_view;

   public:
    sentinel() = default;

    constexpr sentinel(sentinel<!Const> s) requires Const
      && convertible_to<inner_sentinel<false>, inner_sentinel<Const>>
      : inner_(std::move(s.inner_)) { }

    template<bool OtherConst>
      requires sentinel_for<inner_sentinel<Const>, inner_iterator<OtherConst>>
    friend constexpr bool
    operator==(const iterator<OtherConst>& x, const sentinel& y) {
      return x.inner_ == y.inner_;
    }

    template<bool OtherConst>
      requires sized_sentinel_for<inner_sentinel<Const>, inner_iterator<OtherConst>>
    friend constexpr maybe_const_difference_t<OtherConst, InnerView>
    operator-(const iterator<OtherConst>& x, const sentinel& y) {
      return x.inner_ - y.inner_;
    }

    template<bool OtherConst>
      requires sized_sentinel_for<inner_sentinel<Const>, inner_iterator<OtherConst>>
    friend constexpr maybe_const_difference_t<OtherConst, InnerView>
    operator-(const sentinel& x, const iterator<OtherConst>& y) {
      return x.inner_ - y.inner_;
    }
  };

 public:
  adjacent_transform_view() = default;

  constexpr explicit adjacent_transform_view(V base, F fun)
    : inner_(std::move(base)), fun_(std::move(fun)) { }

  constexpr auto
  begin() {
    return iterator<false>(*this, inner_.begin());
  }

  constexpr auto
  begin() const requires range<const InnerView> &&
    repeat_regular_invocable<const F&, range_reference_t<const V>, N> {
    return iterator<true>(*this, inner_.begin());
  }

  constexpr auto
  end() {
    if constexpr (common_range<InnerView>)
      return iterator<false>(*this, inner_.end());
    else
      return sentinel<false>(inner_.end());
  }

  constexpr auto
  end() const requires range<const InnerView> &&
    repeat_regular_invocable<const F&, range_reference_t<const V>, N> {
    if constexpr (common_range<const InnerView>)
      return iterator<true>(*this, inner_.end());
    else
      return sentinel<true>(inner_.end());
  }

  constexpr auto
  size() requires sized_range<InnerView> {
    return inner_.size();
  }

  constexpr auto
  size() const requires sized_range<const InnerView> {
    return inner_.size();
  }
};

}  // namespace std::ranges

namespace std::ranges {

template<forward_range V, indirect_binary_predicate<iterator_t<V>, iterator_t<V>> Pred>
  requires view<V> && is_object_v<Pred>
class chunk_by_view : public view_interface<chunk_by_view<V, Pred>> {
  V base_ = V();
  [[no_unique_address]] __detail::__box<Pred> pred_ = Pred();
  [[no_unique_address]] __detail::_CachedPosition<V> cached_begin_;

  class iterator {
    chunk_by_view* parent_ = nullptr;
    iterator_t<V> current_ = iterator_t<V>();
    iterator_t<V> next_ = iterator_t<V>();

    constexpr iterator(chunk_by_view& parent, iterator_t<V> current, iterator_t<V> next)
      : parent_(addressof(parent)), current_(current), next_(next) { }

    friend chunk_by_view;

   public:
    using value_type = subrange<iterator_t<V>>;
    using difference_type = range_difference_t<V>;
    using iterator_category = input_iterator_tag;
    using iterator_concept =
      conditional_t<bidirectional_range<V>, bidirectional_iterator_tag, forward_iterator_tag>;

    iterator() = default;

    constexpr value_type
    operator*() const {
      return subrange(current_, next_);
    }

    constexpr iterator&
    operator++() {
      current_ = next_;
      next_ = parent_->find_next(current_);
      return *this;
    }

    constexpr iterator
    operator++(int) {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires bidirectional_range<V> {
      next_ = current_;
      current_ = parent_->find_prev(next_);
      return *this;
    }

    constexpr iterator
    operator--(int) requires bidirectional_range<V> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    friend constexpr bool
    operator==(const iterator& x, const iterator& y) {
      return x.current_ == y.current_;
    }

    friend constexpr bool
    operator==(const iterator& x, default_sentinel_t) {
      return x.current_ == x.next_;
    }
  };

 public:
  chunk_by_view() requires((default_initializable<V> && default_initializable<Pred>)) = default;

  constexpr explicit chunk_by_view(V base, Pred pred)
    : base_(std::move(base)), pred_(std::move(pred)) { }

  constexpr V
  base() const& requires copy_constructible<V> {
    return base_;
  }

  constexpr V
  base() && {
    return std::move(base_);
  }

  constexpr const Pred&
  pred() const {
    return *pred_;
  }

  constexpr iterator
  begin() {
    if (cached_begin_._M_has_value())
      return {*this, ranges::begin(base_), cached_begin_._M_get(base_)};

    auto it = find_next(ranges::begin(base_));
    cached_begin_._M_set(base_, it);
    return {*this, ranges::begin(base_), std::move(it)};
  }

  constexpr auto
  end() {
    if constexpr (common_range<V>)
      return iterator(*this, ranges::end(base_), ranges::end(base_));
    else
      return default_sentinel;
  }

  constexpr iterator_t<V>
  find_next(iterator_t<V> current) {
    return ranges::next(ranges::adjacent_find(current, ranges::end(base_), not_fn(ref(*pred_))), 1,
                        ranges::end(base_));
  }

  constexpr iterator_t<V>
  find_prev(iterator_t<V> current) requires bidirectional_range<V> {
    using namespace std::placeholders;
    reverse_view rv(subrange(ranges::begin(base_), current));
    return ranges::prev(ranges::adjacent_find(rv, not_fn(bind(ref(*pred_), _2, _1))).base(), 1,
                        ranges::begin(base_));
  }
};

template<class R, class Pred>
chunk_by_view(R&&, Pred) -> chunk_by_view<views::all_t<R>, Pred>;

}  // namespace std::ranges

namespace std::ranges {

template<class R, class P>
concept compatible_joinable_ranges = common_with<range_value_t<R>, range_value_t<P>> &&
  common_reference_with<range_reference_t<R>, range_reference_t<P>> &&
  common_reference_with<range_rvalue_reference_t<R>, range_rvalue_reference_t<P>>;

template<class R>
concept bidirectional_common = bidirectional_range<R> && common_range<R>;

template<input_range V, forward_range Pattern>
  requires view<V> && input_range<range_value_t<V>> && view<Pattern> &&
    compatible_joinable_ranges<range_reference_t<V>, Pattern>
class join_with_view : public view_interface<join_with_view<V, Pattern>> {
  using InnerRng = range_reference_t<V>;

  V base_ = V();
  [[no_unique_address]] __detail::__non_propagating_cache<remove_cv_t<InnerRng>> inner_;
  Pattern pattern_ = Pattern();

  template<bool Const>
  using Parent = maybe_const<Const, join_with_view>;
  template<bool Const>
  using Base = maybe_const<Const, V>;
  template<bool Const>
  using InnerBase = range_reference_t<Base<Const>>;
  template<bool Const>
  using PatternBase = maybe_const<Const, Pattern>;

  template<bool Const>
  struct join_with_iter_cat { };

  template<bool Const>
    requires is_reference_v<InnerBase<Const>> && forward_range<Base<Const>> &&
      forward_range<InnerBase<Const>>
  struct join_with_iter_cat<Const> {
    using iterator_category = decltype([] {
      using Base = join_with_view::Base<Const>;
      using InnerBase = join_with_view::InnerBase<Const>;
      using PatternBase = join_with_view::PatternBase<Const>;

      using OuterIter = iterator_t<Base>;
      using InnerIter = iterator_t<InnerBase>;
      using PatternIter = iterator_t<PatternBase>;

      using OuterCat = iterator_traits<OuterIter>::iterator_category;
      using InnerCat = iterator_traits<InnerIter>::iterator_category;
      using PatternCat = iterator_traits<PatternIter>::iterator_category;

      if constexpr (!is_lvalue_reference_v<common_reference_t<iter_reference_t<InnerIter>,
                                                              iter_reference_t<PatternIter>>>)
        return input_iterator_tag{};
      else if constexpr (derived_from<OuterCat, bidirectional_iterator_tag> &&
                         derived_from<InnerCat, bidirectional_iterator_tag> &&
                         derived_from<PatternCat, bidirectional_iterator_tag> &&
                         common_range<InnerBase> && common_range<PatternBase>)
        return bidirectional_iterator_tag{};
      else if constexpr (derived_from<OuterCat, forward_iterator_tag> &&
                         derived_from<InnerCat, forward_iterator_tag> &&
                         derived_from<PatternCat, forward_iterator_tag>)
        return forward_iterator_tag{};
      else
        return input_iterator_tag{};
    }());
  };

  template<bool Const>
  class iterator : public join_with_iter_cat<Const> {
    using Parent = join_with_view::Parent<Const>;
    using Base = join_with_view::Base<Const>;
    using InnerBase = join_with_view::InnerBase<Const>;
    using PatternBase = join_with_view::PatternBase<Const>;

    using OuterIter = iterator_t<Base>;
    using InnerIter = iterator_t<InnerBase>;
    using PatternIter = iterator_t<PatternBase>;

    static constexpr bool ref_is_glvalue = is_reference_v<InnerBase>;

    Parent* parent_ = nullptr;
    OuterIter outer_it_ = OuterIter();
    variant<PatternIter, InnerIter> inner_it_;

    constexpr iterator(Parent& parent, iterator_t<Base> outer)
      : parent_(addressof(parent)), outer_it_(std::move(outer)) {
      if (outer_it_ != ranges::end(parent_->base_)) {
        auto&& inner = update_inner(outer_it_);
        inner_it_.template emplace<1>(ranges::begin(inner));
        satisfy();
      }
    }

    constexpr auto&&
    update_inner(const OuterIter& x) {
      if constexpr (ref_is_glvalue)
        return *x;
      else
        return parent_->inner_._M_emplace_deref(x);
    }

    constexpr auto&&
    get_inner(const OuterIter& x) {
      if constexpr (ref_is_glvalue)
        return *x;
      else
        return *parent_->inner_;
    }

    // join_with_view iterators use the satisfy function to skip over empty inner ranges.
    constexpr void
    satisfy() {
      while (true) {
        if (inner_it_.index() == 0) {
          if (get<0>(inner_it_) != ranges::end(parent_->pattern_))
            break;

          auto&& inner = update_inner(outer_it_);
          inner_it_.template emplace<1>(ranges::begin(inner));
        } else {
          auto&& inner = get_inner(outer_it_);
          if (get<1>(inner_it_) != ranges::end(inner))
            break;

          if (++outer_it_ == ranges::end(parent_->base_)) {
            if constexpr (ref_is_glvalue)
              inner_it_.template emplace<0>();
            break;
          }

          inner_it_.template emplace<0>(ranges::begin(parent_->pattern_));
        }
      }
    }

    friend Parent;

   public:
    using iterator_concept = decltype([] {
      if constexpr (ref_is_glvalue && bidirectional_range<Base> &&
                    bidirectional_common<InnerBase> && bidirectional_common<PatternBase>)
        return bidirectional_iterator_tag{};
      else if constexpr (ref_is_glvalue && forward_range<Base> && forward_range<InnerBase>)
        return forward_iterator_tag{};
      else
        return input_iterator_tag{};
    }());
    using value_type = common_type_t<iter_value_t<InnerIter>, iter_value_t<PatternIter>>;
    using difference_type =
      common_type_t<iter_difference_t<OuterIter>, iter_difference_t<InnerIter>,
                    iter_difference_t<PatternIter>>;

    iterator() requires(default_initializable<OuterIter>) = default;

    constexpr iterator(iterator<!Const> i) requires Const &&
      (convertible_to<iterator_t<V>, OuterIter>&& convertible_to<iterator_t<InnerRng>, InnerIter>&&
         convertible_to<iterator_t<Pattern>, PatternIter>)
      : parent_(i.parent_), outer_it_(std::move(i.outer_it_)) {
      if (i.inner_it_.index() == 0)
        inner_it_.template emplace<0>(get<0>(std::move(i.inner_it_)));
      else
        inner_it_.template emplace<1>(get<1>(std::move(i.inner_it_)));
    }

    constexpr decltype(auto)
    operator*() const {
      using reference =
        common_reference_t<iter_reference_t<InnerIter>, iter_reference_t<PatternIter>>;
      return visit([](auto& it) -> reference { return *it; }, inner_it_);
    }

    constexpr iterator&
    operator++() {
      visit([](auto& it) { ++it; }, inner_it_);
      satisfy();
      return *this;
    }

    constexpr void
    operator++(int) {
      ++*this;
    }

    constexpr iterator
    operator++(int) requires ref_is_glvalue
      && forward_iterator<OuterIter> && forward_iterator<InnerIter> {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires ref_is_glvalue && bidirectional_range<Base> &&
      bidirectional_common<InnerBase> && bidirectional_common<PatternBase> {
      if (outer_it_ == ranges::end(parent_->base_)) {
        auto&& inner = *--outer_it_;
        inner_it_.template emplace<1>(ranges::end(inner));
      }

      // bidirectional satisfy
      while (true) {
        if (inner_it_.index() == 0) {
          auto& it = get<0>(inner_it_);
          if (it == ranges::begin(parent_->pattern_)) {
            auto&& inner = *--outer_it_;
            inner_it_.template emplace<1>(ranges::end(inner));
          } else
            break;

        } else {
          auto& it = get<1>(inner_it_);
          auto&& inner = *outer_it_;
          if (it == ranges::begin(inner))
            inner_it_.template emplace<0>(ranges::end(parent_->pattern_));
          else
            break;
        }
      }

      visit([](auto& it) { --it; }, inner_it_);
      return *this;
    }

    constexpr iterator
    operator--(int) requires ref_is_glvalue && bidirectional_range<Base> &&
      bidirectional_common<InnerBase> && bidirectional_common<PatternBase> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    friend constexpr bool
    operator==(const iterator& x, const iterator& y) requires ref_is_glvalue
      && equality_comparable<OuterIter> && equality_comparable<InnerIter> {
      return x.outer_it_ == y.outer_it_ && x.inner_it_ == y.inner_it_;
    }

    friend constexpr decltype(auto)
    iter_move(const iterator& x) {
      using rvalue_reference = common_reference_t<iter_rvalue_reference_t<InnerIter>,
                                                  iter_rvalue_reference_t<PatternIter>>;
      return visit<rvalue_reference>(ranges::iter_move, x.inner_it_);
    }

    friend constexpr void
    iter_swap(const iterator& x,
              const iterator& y) requires indirectly_swappable<InnerIter, PatternIter> {
      visit(ranges::iter_swap, x.inner_it_, y.inner_it_);
    }
  };

  template<bool Const>
  class sentinel {
    using Parent = join_with_view::Parent<Const>;
    using Base = join_with_view::Base<Const>;
    sentinel_t<Base> end_ = sentinel_t<Base>();

    constexpr explicit sentinel(Parent& parent) : end_(ranges::end(parent.base_)) { }

    friend Parent;

    template<bool OtherConst>
    constexpr auto
    equal_to(const iterator<OtherConst>& x) const {
      return x.outer_it_ == end_;
    }

   public:
    sentinel() = default;

    constexpr sentinel(sentinel<!Const> s) requires Const &&
      (convertible_to<sentinel_t<V>, sentinel_t<Base>>)
      : end_(std::move(s.end_)) { }

    template<bool OtherConst>
      requires sentinel_for<sentinel_t<Base>, iterator_t<join_with_view::Base<OtherConst>>>
    friend constexpr bool
    operator==(const iterator<OtherConst>& x, const sentinel& y) {
      return y.equal_to(x);
    }
  };

 public:
  join_with_view() requires((default_initializable<V> && default_initializable<Pattern>)) = default;

  constexpr join_with_view(V base, Pattern pattern)
    : base_(std::move(base)), pattern_(std::move(pattern)) { }

  template<input_range R>
    requires constructible_from<V, views::all_t<R>> &&
      constructible_from<Pattern, single_view<range_value_t<InnerRng>>>
  constexpr join_with_view(R&& r, range_value_t<InnerRng> e)
    : base_(views::all(std::forward<R>(r))), pattern_(views::single(std::move(e))) { }

  constexpr V
  base() const& requires copy_constructible<V> {
    return base_;
  }

  constexpr V
  base() && {
    return std::move(base_);
  }

  constexpr auto
  begin() {
    constexpr bool use_const = simple_view<V> && is_reference_v<InnerRng> && simple_view<Pattern>;
    return iterator<use_const>{*this, ranges::begin(base_)};
  }

  constexpr auto
  begin() const requires input_range<const V> && forward_range<const Pattern> &&
    input_range<range_reference_t<const V>> && is_reference_v<range_reference_t<const V>> {
    return iterator<true>{*this, ranges::begin(base_)};
  }

  constexpr auto
  end() {
    constexpr bool use_const = simple_view<V> && simple_view<Pattern>;
    if constexpr (forward_range<V> && is_reference_v<InnerRng> && forward_range<InnerRng> &&
                  common_range<V> && common_range<InnerRng>)
      return iterator<use_const>{*this, ranges::end(base_)};
    else
      return sentinel<use_const>{*this};
  }

  constexpr auto
  end() const requires input_range<const V> && forward_range<const Pattern> &&
    input_range<range_reference_t<const V>> && is_reference_v<range_reference_t<const V>> {
    using InnerConstRng = range_reference_t<const V>;
    if constexpr (forward_range<const V> && forward_range<InnerConstRng> && common_range<const V> &&
                  common_range<InnerConstRng>)
      return iterator<true>{*this, ranges::end(base_)};
    else
      return sentinel<true>{*this};
  }
};

template<class R, class P>
join_with_view(R&&, P&&) -> join_with_view<views::all_t<R>, views::all_t<P>>;

template<input_range R>
join_with_view(R&&, range_value_t<range_reference_t<R>>)
  -> join_with_view<views::all_t<R>, single_view<range_value_t<range_reference_t<R>>>>;

}  // namespace std::ranges

namespace std::ranges {

template<class I>
constexpr I
div_ceil(I num, I denom) {
  I r = num / denom;
  if (num % denom)
    ++r;
  return r;
}

template<view V>
class chunk_view;

template<view V>
  requires input_range<V>
class chunk_view<V> : public view_interface<chunk_view<V>> {
  V base_;
  range_difference_t<V> n_;
  range_difference_t<V> remainder_ = 0;

  std::optional<iterator_t<V>> current_;

  friend class outer_iterator;
  class outer_iterator {
    chunk_view* parent_;

    constexpr explicit outer_iterator(chunk_view& parent) : parent_(addressof(parent)) { }

    friend chunk_view;

    constexpr bool
    reach_end() const {
      return *parent_->current_ == ranges::end(parent_->base_) && parent_->remainder_ != 0;
    }

    constexpr auto
    from_end() const {
      const auto dist = ranges::end(parent_->base_) - *parent_->current_;
      if (dist < parent_->remainder_)
        return dist == 0 ? 0 : 1;
      return div_ceil(dist - parent_->remainder_, parent_->n_) + 1;
    }

   public:
    using iterator_concept = input_iterator_tag;
    using difference_type = range_difference_t<V>;

    class value_type : view_interface<value_type> {
      chunk_view* parent_;

      constexpr explicit value_type(chunk_view& parent) : parent_(addressof(parent)) { }

      friend class outer_iterator;

     public:
      class inner_iterator {
        chunk_view* parent_;

        constexpr explicit inner_iterator(chunk_view& parent) noexcept
          : parent_(addressof(parent)) { }

        constexpr bool
        reach_end() const {
          return parent_->remainder_ == 0;
        }

        constexpr auto
        from_end() const {
          return ranges::min(parent_->remainder_, ranges::end(parent_->base_) - *parent_->current_);
        }

        friend class value_type;

       public:
        using iterator_concept = input_iterator_tag;
        using difference_type = range_difference_t<V>;
        using value_type = range_value_t<V>;

        inner_iterator(inner_iterator&&) = default;
        inner_iterator& operator=(inner_iterator&&) = default;

        constexpr const iterator_t<V>&
        base() const& noexcept {
          return *parent_->current_;
        }

        constexpr range_reference_t<V>
        operator*() const {
          return **parent_->current_;
        }

        constexpr inner_iterator&
        operator++() {
          ++*parent_->current_;
          if (*parent_->current_ == ranges::end(parent_->base_))
            parent_->remainder_ = 0;
          else
            --parent_->remainder_;
          return *this;
        }

        constexpr void
        operator++(int) {
          ++*this;
        }

        friend constexpr bool
        operator==(const inner_iterator& x, default_sentinel_t) {
          return x.reach_end();
        }

        friend constexpr difference_type
        operator-(default_sentinel_t y, const inner_iterator& x) requires
          sized_sentinel_for<sentinel_t<V>, iterator_t<V>> {
          return x.from_end();
        }

        friend constexpr difference_type
        operator-(const inner_iterator& x,
                  default_sentinel_t y) requires sized_sentinel_for<sentinel_t<V>, iterator_t<V>> {
          return -(y - x);
        }
      };

     public:
      constexpr inner_iterator
      begin() const noexcept {
        return inner_iterator(*parent_);
      }

      constexpr default_sentinel_t
      end() const noexcept {
        return default_sentinel;
      }

      constexpr auto
      size() const requires sized_sentinel_for<sentinel_t<V>, iterator_t<V>> {
        return __detail::__to_unsigned_like(
          ranges::min(parent_->remainder_, ranges::end(parent_->base_) - *parent_->current_));
      }
    };

    outer_iterator(outer_iterator&&) = default;
    outer_iterator& operator=(outer_iterator&&) = default;

    constexpr value_type
    operator*() const {
      return value_type(*parent_);
    }

    constexpr outer_iterator&
    operator++() {
      ranges::advance(*parent_->current_, parent_->remainder_, ranges::end(parent_->base_));
      parent_->remainder_ = parent_->n_;
      return *this;
    }

    constexpr void
    operator++(int) {
      ++*this;
    }

    friend constexpr bool
    operator==(const outer_iterator& x, default_sentinel_t) {
      return x.reach_end();
    }

    friend constexpr difference_type
    operator-(default_sentinel_t y,
              const outer_iterator& x) requires sized_sentinel_for<sentinel_t<V>, iterator_t<V>> {
      return x.from_end();
    }

    friend constexpr difference_type
    operator-(const outer_iterator& x,
              default_sentinel_t y) requires sized_sentinel_for<sentinel_t<V>, iterator_t<V>> {
      return -(y - x);
    }
  };

 public:
  constexpr explicit chunk_view(V base, range_difference_t<V> n) : base_(std::move(base)), n_(n) { }

  constexpr V
  base() const& requires copy_constructible<V> {
    return base_;
  }

  constexpr V
  base() && {
    return std::move(base_);
  }

  constexpr outer_iterator
  begin() {
    current_ = ranges::begin(base_);
    remainder_ = n_;
    return outer_iterator(*this);
  }

  constexpr default_sentinel_t
  end() const noexcept {
    return default_sentinel;
  }

  constexpr auto
  size() requires sized_range<V> {
    return __detail::__to_unsigned_like(div_ceil(ranges::distance(base_), n_));
  }

  constexpr auto
  size() const requires sized_range<const V> {
    return __detail::__to_unsigned_like(div_ceil(ranges::distance(base_), n_));
  }
};

template<view V>
  requires forward_range<V>
class chunk_view<V> : public view_interface<chunk_view<V>> {
  V base_;
  range_difference_t<V> n_;

  template<bool Const>
  class iterator {
    using Parent = maybe_const<Const, chunk_view>;
    using Base = maybe_const<Const, V>;

    iterator_t<Base> current_ = iterator_t<Base>();
    sentinel_t<Base> end_ = sentinel_t<Base>();
    range_difference_t<Base> n_ = 0;
    range_difference_t<Base> missing_ = 0;

    constexpr iterator(Parent* parent, iterator_t<Base> current,
                       range_difference_t<Base> missing = 0)
      : current_(current), end_(ranges::end(parent->base_)), n_(parent->n_), missing_(missing) { }

    friend chunk_view;

   public:
    using iterator_category = input_iterator_tag;
    using iterator_concept = conditional_t<
      random_access_range<Base>, random_access_iterator_tag,
      conditional_t<bidirectional_range<Base>, bidirectional_iterator_tag, forward_iterator_tag>>;
    using value_type = decltype(views::take(subrange(current_, end_), n_));
    using difference_type = range_difference_t<Base>;

    iterator() = default;

    constexpr iterator(iterator<!Const> i) requires Const &&
      (convertible_to<iterator_t<V>, iterator_t<Base>>&&
         convertible_to<sentinel_t<V>, sentinel_t<Base>>)
      : current_(std::move(i.current_)), end_(std::move(i.end_)), n_(i.n_), missing_(i.missing_) { }

    constexpr iterator_t<Base>
    base() const {
      return current_;
    }

    constexpr value_type
    operator*() const {
      return views::take(subrange(current_, end_), n_);
    }

    constexpr iterator&
    operator++() {
      missing_ = ranges::advance(current_, n_, end_);
      return *this;
    }

    constexpr iterator
    operator++(int) {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires bidirectional_range<Base> {
      ranges::advance(current_, missing_ - n_);
      missing_ = 0;
      return *this;
    }

    constexpr iterator
    operator--(int) requires bidirectional_range<Base> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type x) requires random_access_range<Base> {
      if (x > 0)
        missing_ = ranges::advance(current_, n_ * x, end_);
      else if (x < 0) {
        ranges::advance(current_, n_ * x + missing_);
        missing_ = 0;
      }
      return *this;
    }

    constexpr iterator&
    operator-=(difference_type x) requires random_access_range<Base> {
      return *this += -x;
    }

    constexpr value_type
    operator[](difference_type n) const requires random_access_range<Base> {
      return *(*this + n);
    }

    friend constexpr bool
    operator==(const iterator& x, const iterator& y) {
      return x.current_ == y.current_;
    }

    friend constexpr bool
    operator==(const iterator& x, default_sentinel_t) {
      return x.current_ == x.end_;
    }

    friend constexpr bool
    operator<(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.current_ < y.current_;
    }

    friend constexpr bool
    operator>(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return y < x;
    }

    friend constexpr bool
    operator<=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(y < x);
    }

    friend constexpr bool
    operator>=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(x < y);
    }

    friend constexpr auto
    operator<=>(const iterator& x, const iterator& y) requires random_access_range<Base> &&
      three_way_comparable<iterator_t<Base>> {
      return x.current_ <=> y.current_;
    }

    friend constexpr iterator
    operator+(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator+(difference_type n, const iterator& i) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator-(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r -= n;
      return r;
    }

    friend constexpr difference_type
    operator-(const iterator& x,
              const iterator& y) requires sized_sentinel_for<iterator_t<Base>, iterator_t<Base>> {
      return (x.current_ - y.current_ + x.missing_ - y.missing_) / x.n_;
    }

    friend constexpr difference_type
    operator-(default_sentinel_t y,
              const iterator& x) requires sized_sentinel_for<sentinel_t<Base>, iterator_t<Base>> {
      return div_ceil(x.end_ - x.current_, x.n_);
    }

    friend constexpr difference_type
    operator-(const iterator& x, default_sentinel_t y) requires
      sized_sentinel_for<sentinel_t<Base>, iterator_t<Base>> {
      return -(y - x);
    }
  };

 public:
  constexpr explicit chunk_view(V base, range_difference_t<V> n) : base_(std::move(base)), n_(n) { }

  constexpr V
  base() const& requires copy_constructible<V> {
    return base_;
  }

  constexpr V
  base() && {
    return std::move(base_);
  }

  constexpr auto
  begin() requires(!simple_view<V>) {
    return iterator<false>(this, ranges::begin(base_));
  }

  constexpr auto
  begin() const requires forward_range<const V> {
    return iterator<true>(this, ranges::begin(base_));
  }

  constexpr auto
  end() requires(!simple_view<V>) {
    if constexpr (common_range<V> && sized_range<V>) {
      auto missing = (n_ - ranges::distance(base_) % n_) % n_;
      return iterator<false>(this, ranges::end(base_), missing);
    } else if constexpr (common_range<V> && !bidirectional_range<V>)
      return iterator<false>(this, ranges::end(base_));
    else
      return default_sentinel;
  }

  constexpr auto
  end() const requires forward_range<const V> {
    if constexpr (common_range<const V> && sized_range<const V>) {
      auto missing = (n_ - ranges::distance(base_) % n_) % n_;
      return iterator<true>(this, ranges::end(base_), missing);
    } else if constexpr (common_range<const V> && !bidirectional_range<const V>)
      return iterator<true>(this, ranges::end(base_));
    else
      return default_sentinel;
  }

  constexpr auto
  size() requires sized_range<V> {
    return __detail::__to_unsigned_like(div_ceil(ranges::distance(base_), n_));
  }

  constexpr auto
  size() const requires sized_range<const V> {
    return __detail::__to_unsigned_like(div_ceil(ranges::distance(base_), n_));
  }
};

template<class R>
chunk_view(R&& r, range_difference_t<R>) -> chunk_view<views::all_t<R>>;

}  // namespace std::ranges

namespace std::ranges {

template<class V>
concept slide_caches_nothing = random_access_range<V> && sized_range<V>;

template<class V>
concept slide_caches_last = !slide_caches_nothing<V> && bidirectional_range<V> && common_range<V>;

template<class V>
concept slide_caches_first = !slide_caches_nothing<V> && !slide_caches_last<V>;

template<forward_range V>
  requires view<V>
class slide_view : public view_interface<slide_view<V>> {
  V base_;
  range_difference_t<V> n_;
  [[no_unique_address]] __detail::__maybe_present_t<slide_caches_first<V> || slide_caches_last<V>,
                                                    __detail::_CachedPosition<V>>
    cached_begin_;

  template<bool Const>
  class iterator {
    using Base = maybe_const<Const, V>;

    iterator_t<Base> current_ = iterator_t<Base>();
    [[no_unique_address]] __detail::__maybe_present_t<slide_caches_first<Base>, iterator_t<Base>>
      last_ele_;
    range_difference_t<Base> n_ = 0;

    constexpr iterator(iterator_t<Base> current,
                       range_difference_t<Base> n) requires(!slide_caches_first<Base>)
      : current_(current), n_(n) { }

    constexpr iterator(iterator_t<Base> current, iterator_t<Base> last_ele,
                       range_difference_t<Base> n) requires(slide_caches_first<Base>)
      : current_(current), last_ele_(last_ele), n_(n) { }

    friend slide_view;

   public:
    using iterator_category = input_iterator_tag;
    using iterator_concept = conditional_t<
      random_access_range<Base>, random_access_iterator_tag,
      conditional_t<bidirectional_range<Base>, bidirectional_iterator_tag, forward_iterator_tag>>;
    using value_type = decltype(views::counted(current_, n_));
    using difference_type = range_difference_t<Base>;

    iterator() = default;

    constexpr iterator(iterator<!Const> i) requires Const &&
      (convertible_to<iterator_t<V>, iterator_t<Base>>)
      : current_(std::move(i.current_)), n_(i.n_) { }

    constexpr auto
    operator*() const {
      return views::counted(current_, n_);
    }

    constexpr iterator&
    operator++() {
      current_ = ranges::next(current_);
      if constexpr (slide_caches_first<Base>)
        last_ele_ = ranges::next(last_ele_);
      return *this;
    }

    constexpr iterator
    operator++(int) {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires bidirectional_range<Base> {
      current_ = ranges::prev(current_);
      if constexpr (slide_caches_first<Base>)
        last_ele_ = ranges::prev(last_ele_);
      return *this;
    }

    constexpr iterator
    operator--(int) requires bidirectional_range<Base> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type x) requires random_access_range<Base> {
      current_ = current_ + x;
      if constexpr (slide_caches_first<Base>)
        last_ele_ = last_ele_ + x;
      return *this;
    }

    constexpr iterator&
    operator-=(difference_type x) requires random_access_range<Base> {
      current_ = current_ - x;
      if constexpr (slide_caches_first<Base>)
        last_ele_ = last_ele_ - x;
      return *this;
    }

    constexpr auto
    operator[](difference_type n) const requires random_access_range<Base> {
      return views::counted(current_ + n, n_);
    }

    friend constexpr bool
    operator==(const iterator& x, const iterator& y) {
      if constexpr (slide_caches_first<Base>)
        return x.last_ele_ == y.last_ele_;
      else
        return x.current_ == y.current_;
    }

    friend constexpr bool
    operator<(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.current_ < y.current_;
    }

    friend constexpr bool
    operator>(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return y < x;
    }

    friend constexpr bool
    operator<=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(y < x);
    }

    friend constexpr bool
    operator>=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(x < y);
    }

    friend constexpr auto
    operator<=>(const iterator& x, const iterator& y) requires random_access_range<Base> &&
      three_way_comparable<iterator_t<Base>> {
      return x.current_ <=> y.current_;
    }

    friend constexpr iterator
    operator+(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator+(difference_type n, const iterator& i) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator-(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r -= n;
      return r;
    }

    friend constexpr difference_type
    operator-(const iterator& x,
              const iterator& y) requires sized_sentinel_for<iterator_t<Base>, iterator_t<Base>> {
      if constexpr (slide_caches_first<Base>)
        return x.last_ele_ - y.last_ele_;
      else
        return x.current_ - y.current_;
    }
  };

  class sentinel {
    sentinel_t<V> end_ = sentinel_t<V>();

    constexpr explicit sentinel(sentinel_t<V> end) : end_(end) { }

    friend slide_view;

   public:
    sentinel() = default;

    friend constexpr bool
    operator==(const iterator<false>& x, const sentinel& y) {
      return x.last_ele_ == y.end_;
    }

    friend constexpr range_difference_t<V>
    operator-(const iterator<false>& x,
              const sentinel& y) requires sized_sentinel_for<sentinel_t<V>, iterator_t<V>> {
      return x.last_ele_ - y.end_;
    }

    friend constexpr range_difference_t<V>
    operator-(const sentinel& y,
              const iterator<false>& x) requires sized_sentinel_for<sentinel_t<V>, iterator_t<V>> {
      return y.end_ - x.last_ele_;
    }
  };

 public:
  constexpr explicit slide_view(V base, range_difference_t<V> n) : base_(std::move(base)), n_(n) { }

  constexpr auto
  begin() requires(!(simple_view<V> && slide_caches_nothing<const V>)) {
    if constexpr (slide_caches_first<V>) {
      if (cached_begin_._M_has_value())
        return iterator<false>(ranges::begin(base_), cached_begin_._M_get(base_), n_);

      auto next = ranges::next(ranges::begin(base_), n_ - 1, ranges::end(base_));
      cached_begin_._M_set(base_, next);
      return iterator<false>(ranges::begin(base_), std::move(next), n_);
    } else
      return iterator<false>(ranges::begin(base_), n_);
  }

  constexpr auto
  begin() const requires slide_caches_nothing<const V> {
    return iterator<true>(ranges::begin(base_), n_);
  }

  constexpr auto
  end() requires(!(simple_view<V> && slide_caches_nothing<const V>)) {
    if constexpr (slide_caches_nothing<V>)
      return iterator<false>(ranges::begin(base_) + range_difference_t<V>(size()), n_);
    else if constexpr (slide_caches_last<V>) {
      if (cached_begin_._M_has_value())
        return iterator<false>(cached_begin_._M_get(base_), n_);

      auto prev = ranges::prev(ranges::end(base_), n_ - 1, ranges::begin(base_));
      cached_begin_._M_set(base_, prev);
      return iterator<false>(std::move(prev), n_);
    } else if constexpr (common_range<V>)
      return iterator<false>(ranges::end(base_), ranges::end(base_), n_);
    else
      return sentinel(ranges::end(base_));
  }

  constexpr auto
  end() const requires slide_caches_nothing<const V> {
    return begin() + range_difference_t<const V>(size());
  }

  constexpr auto
  size() requires sized_range<V> {
    auto sz = ranges::distance(base_) - n_ + 1;
    if (sz < 0)
      sz = 0;
    return __detail::__to_unsigned_like(sz);
  }

  constexpr auto
  size() const requires sized_range<const V> {
    auto sz = ranges::distance(base_) - n_ + 1;
    if (sz < 0)
      sz = 0;
    return __detail::__to_unsigned_like(sz);
  }
};

template<class R>
slide_view(R&& r, range_difference_t<R>) -> slide_view<views::all_t<R>>;

}  // namespace std::ranges

namespace std::ranges {

template<input_range V>
  requires view<V>
class stride_view : public view_interface<stride_view<V>> {
  V base_ = V();
  range_difference_t<V> stride_ = 1;

  template<bool Const>
  using Base = maybe_const<Const, V>;

  template<bool Const>
  struct stride_view_iter_cat { };

  template<bool Const>
    requires forward_range<Base<Const>>
  struct stride_view_iter_cat<Const> {
    using iterator_category = decltype([] {
      using C = iterator_traits<iterator_t<Base<Const>>>::iterator_category;
      if constexpr (derived_from<C, random_access_iterator_tag>)
        return random_access_iterator_tag{};
      else
        return C{};
    }());
  };

  template<bool Const>
  class iterator : public stride_view_iter_cat<Const> {
    using Parent = maybe_const<Const, stride_view>;
    using Base = stride_view::Base<Const>;

    iterator_t<Base> current_ = iterator_t<Base>();
    sentinel_t<Base> end_ = sentinel_t<Base>();
    range_difference_t<Base> stride_ = 0;
    range_difference_t<Base> missing_ = 0;

    constexpr iterator(Parent* parent, iterator_t<Base> current,
                       range_difference_t<Base> missing = 0)
      : current_(std::move(current)),
        end_(ranges::end(parent->base_)),
        stride_(parent->stride_),
        missing_(missing) { }

    friend stride_view;

   public:
    using iterator_category = input_iterator_tag;
    using iterator_concept = decltype([] {
      if constexpr (random_access_range<Base>)
        return random_access_iterator_tag{};
      else if constexpr (bidirectional_range<Base>)
        return bidirectional_iterator_tag{};
      else if constexpr (forward_range<Base>)
        return forward_iterator_tag{};
      else
        return input_iterator_tag{};
    }());

    using value_type = range_difference_t<Base>;
    using difference_type = range_difference_t<Base>;

    iterator() requires(default_initializable<iterator_t<Base>>) = default;

    constexpr iterator(iterator<!Const> i) requires Const &&
      (convertible_to<iterator_t<V>, iterator_t<Base>>&&
         convertible_to<sentinel_t<V>, sentinel_t<Base>>)
      : current_(std::move(i.current_)),
        end_(std::move(i.end_)),
        stride_(i.stride_),
        missing_(i.missing_) { }

    constexpr const iterator_t<Base>&
    base() const& noexcept {
      return current_;
    }

    constexpr iterator_t<Base>
    base() && {
      return std::move(current_);
    }

    constexpr decltype(auto)
    operator*() const {
      return *current_;
    }

    constexpr iterator&
    operator++() {
      missing_ = ranges::advance(current_, stride_, end_);
      return *this;
    }

    constexpr void
    operator++(int) {
      ++*this;
    }

    constexpr iterator
    operator++(int) requires forward_range<Base> {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires bidirectional_range<Base> {
      ranges::advance(current_, missing_ - stride_);
      missing_ = 0;
      return *this;
    }

    constexpr iterator
    operator--(int) requires bidirectional_range<Base> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type x) requires random_access_range<Base> {
      if (x > 0)
        missing_ = ranges::advance(current_, stride_ * x, end_);
      else if (x < 0) {
        ranges::advance(current_, stride_ * x + missing_);
        missing_ = 0;
      }
      return *this;
    }

    constexpr iterator&
    operator-=(difference_type x) requires random_access_range<Base> {
      return *this += -x;
    }

    constexpr value_type
    operator[](difference_type n) const requires random_access_range<Base> {
      return *(*this + n);
    }

    friend constexpr bool
    operator==(const iterator& x,
               const iterator& y) requires equality_comparable<iterator_t<Base>> {
      return x.current_ == y.current_;
    }

    friend constexpr bool
    operator==(const iterator& x, default_sentinel_t) {
      return x.current_ == x.end_;
    }

    friend constexpr bool
    operator<(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return x.current_ < y.current_;
    }

    friend constexpr bool
    operator>(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return y < x;
    }

    friend constexpr bool
    operator<=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(y < x);
    }

    friend constexpr bool
    operator>=(const iterator& x, const iterator& y) requires random_access_range<Base> {
      return !(x < y);
    }

    friend constexpr auto
    operator<=>(const iterator& x, const iterator& y) requires random_access_range<Base> &&
      three_way_comparable<iterator_t<Base>> {
      return x.current_ <=> y.current_;
    }

    friend constexpr iterator
    operator+(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator+(difference_type n, const iterator& i) requires random_access_range<Base> {
      auto r = i;
      r += n;
      return r;
    }

    friend constexpr iterator
    operator-(const iterator& i, difference_type n) requires random_access_range<Base> {
      auto r = i;
      r -= n;
      return r;
    }

    friend constexpr difference_type
    operator-(const iterator& x,
              const iterator& y) requires sized_sentinel_for<iterator_t<Base>, iterator_t<Base>> {
      auto N = x.current_ - y.current_;
      if constexpr (forward_range<Base>)
        return (N + x.missing_ - y.missing_) / x.stride_;
      else if (N < 0)
        return -div_ceil(-N, x.stride_);
      else
        return div_ceil(N, x.stride_);
    }

    friend constexpr difference_type
    operator-(default_sentinel_t y,
              const iterator& x) requires sized_sentinel_for<sentinel_t<Base>, iterator_t<Base>> {
      return div_ceil(x.end_ - x.current_, x.stride_);
    }

    friend constexpr difference_type
    operator-(const iterator& x, default_sentinel_t y) requires
      sized_sentinel_for<sentinel_t<Base>, iterator_t<Base>> {
      return -(y - x);
    }

    friend constexpr range_rvalue_reference_t<Base>
    iter_move(const iterator& i) noexcept(noexcept(ranges::iter_move(i.current_))) {
      return ranges::iter_move(i.current_);
    }

    friend constexpr void
    iter_swap(const iterator& x, const iterator& y) noexcept(noexcept(
      ranges::iter_swap(x.current_, y.current_))) requires indirectly_swappable<iterator_t<Base>> {
      ranges::iter_swap(x.current_, y.current_);
    }
  };

 public:
  stride_view() requires(default_initializable<V>) = default;
  constexpr explicit stride_view(V base, range_difference_t<V> stride)
    : base_(std::move(base)), stride_(stride) { }

  constexpr V
  base() const& requires copy_constructible<V> {
    return base_;
  }

  constexpr V
  base() && {
    return std::move(base_);
  }

  constexpr range_difference_t<V>
  stride() const noexcept {
    return stride_;
  }

  constexpr auto
  begin() requires(!simple_view<V>) {
    return iterator<false>(this, ranges::begin(base_));
  }

  constexpr auto
  begin() const requires range<const V> {
    return iterator<true>(this, ranges::begin(base_));
  }

  constexpr auto
  end() requires(!simple_view<V>) {
    if constexpr (common_range<V> && sized_range<V> && forward_range<V>) {
      auto missing = (stride_ - std::distance(base_) % stride_) % stride_;
      return iterator<false>(this, ranges::end(base_), missing);
    } else if constexpr (common_range<V> && !bidirectional_range<V>)
      return iterator<false>(this, ranges::end(base_));
    else
      return std::default_sentinel;
  }

  constexpr auto
  end() const requires range<const V> {
    if constexpr (common_range<V> && sized_range<V> && forward_range<V>) {
      auto missing = (stride_ - std::ranges::distance(base_) % stride_) % stride_;
      return iterator<true>(this, ranges::end(base_), missing);
    } else if constexpr (common_range<V> && !bidirectional_range<V>)
      return iterator<true>(this, ranges::end(base_));
    else
      return std::default_sentinel;
  }

  constexpr auto
  size() requires sized_range<V> {
    return __detail::__to_unsigned_like(div_ceil(ranges::distance(base_), stride_));
  }

  constexpr auto
  size() const requires sized_range<const V> {
    return __detail::__to_unsigned_like(div_ceil(ranges::distance(base_), stride_));
  }
};

template<class R>
stride_view(R&&, range_difference_t<R>) -> stride_view<std::views::all_t<R>>;

}  // namespace std::ranges

namespace std::ranges {

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

template<input_range First, forward_range... Views>
  requires((view<First> && ... && view<Views>))
class cartesian_product_view : public view_interface<cartesian_product_view<First, Views...>> {
  tuple<First, Views...> bases_;

  template<bool Const>
  struct iterator {
    using iterator_category = input_iterator_tag;
    using iterator_concept = decltype([] {
      if constexpr (cartesian_is_random_access<First, Views...>)
        return random_access_iterator_tag{};
      else if constexpr (cartesian_is_bidirectional<First, Views...>)
        return bidirectional_iterator_tag{};
      else if constexpr (forward_range<First>)
        return forward_iterator_tag{};
      else
        return input_iterator_tag{};
    }());
    using value_type =
      tuple_or_pair<maybe_const_value_t<Const, First>, maybe_const_value_t<Const, Views>...>;
    using reference = tuple_or_pair<maybe_const_reference_t<Const, First>,
                                    maybe_const_reference_t<Const, Views>...>;
    using difference_type = ptrdiff_t;

   private:
    using iter_tuple = iter_tuple_or_pair<Const, First, Views...>;
    using Parent = maybe_const<Const, cartesian_product_view>;
    Parent* parent_;
    iter_tuple current_{};

    friend Parent;

    template<size_t N = sizeof...(Views)>
    constexpr void
    next() {
      auto& it = get<N>(current_);
      ++it;
      if constexpr (N > 0) {
        if (it == ranges::end(get<N>(parent_->bases_))) {
          it = ranges::begin(get<N>(parent_->bases_));
          next<N - 1>();
        }
      }
    }

    template<size_t N = sizeof...(Views)>
    constexpr void
    prev() {
      auto& it = get<N>(current_);
      if (it == ranges::begin(get<N>(parent_->bases_))) {
        ranges::advance(it, cartesian_common_arg_end(get<N>(parent_->bases_)));
        if constexpr (N > 0)
          prev<N - 1>();
      }
      --it;
    }

    template<size_t N>
    constexpr auto
    scaled_size() const {
      if constexpr (N < sizeof...(Views))
        return static_cast<difference_type>(ranges::size(get<N>(parent_->bases_))) *
          scaled_size<N + 1>();
      else
        return static_cast<difference_type>(1);
    }

    template<size_t N, class Tuple>
    constexpr auto
    scaled_distance(Tuple& t) const {
      return static_cast<difference_type>(get<N>(current_) - get<N>(t)) * scaled_size<N + 1>();
    }

    template<class Tuple>
    constexpr auto
    distance_to(Tuple& t) const {
      return [&]<size_t... Is>(index_sequence<Is...>) {
        return (scaled_distance<Is>(t) + ...);
      }
      (index_sequence_for<First, Views...>{});
    }

   public:
    iterator() = default;
    constexpr explicit iterator(Parent& parent, iter_tuple current)
      : parent_(addressof(parent)), current_(std::move(current)) { }

    constexpr iterator(iterator<!Const> i) requires Const &&
      (convertible_to<iterator_t<First>, maybe_const_iterator_t<Const, First>> &&
       (... && convertible_to<iterator_t<Views>, maybe_const_iterator_t<Const, Views>>))
      : parent_(i.parent), current_(std::move(i.current_)) { }

    constexpr auto
    operator*() const {
      return tuple_transform([](auto& i) -> decltype(auto) { return *i; }, current_);
    }

    constexpr iterator&
    operator++() {
      next();
      return *this;
    }

    constexpr iterator
    operator++(int) {
      auto tmp = *this;
      ++*this;
      return tmp;
    }

    constexpr iterator&
    operator--() requires
      cartesian_is_bidirectional<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      prev();
      return *this;
    }

    constexpr iterator
    operator--(int) requires
      cartesian_is_bidirectional<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      auto tmp = *this;
      --*this;
      return tmp;
    }

    constexpr iterator&
    operator+=(difference_type n) requires
      cartesian_is_random_access<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      if (n > 0)
        while (n--)
          next();
      else
        while (n++)
          prev();
    }

    constexpr iterator&
    operator-=(difference_type n) requires
      cartesian_is_random_access<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      *this += -n;
      return *this;
    }

    constexpr reference
    operator[](difference_type n) requires
      cartesian_is_random_access<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      return *(*this + n);
    }

    constexpr friend bool
    operator==(const iterator& x, const iterator& y) requires(
      equality_comparable<maybe_const_iterator_t<Const, First>> &&
      (... && equality_comparable<maybe_const_iterator_t<Const, Views>>)) {
      return x.current_ == y.current_;
    }

    constexpr friend bool
    operator==(const iterator& x, std::default_sentinel_t) {
      return get<0>(x.current_) == ranges::end(get<0>(x.parent_.bases_));
    }

    constexpr friend bool
    operator<(const iterator& x,
              const iterator& y) requires(random_access_range<maybe_const<Const, First>> &&
                                          (... && random_access_range<maybe_const<Const, Views>>)) {
      return x.current_ < y.current_;
    }

    constexpr friend bool
    operator>(const iterator& x,
              const iterator& y) requires(random_access_range<maybe_const<Const, First>> &&
                                          (... && random_access_range<maybe_const<Const, Views>>)) {
      return y < x;
    }

    constexpr friend bool
    operator<=(const iterator& x,
               const iterator& y) requires(random_access_range<maybe_const<Const, First>> &&
                                           (... &&
                                            random_access_range<maybe_const<Const, Views>>)) {
      return !(y < x);
    }

    constexpr friend bool
    operator>=(const iterator& x,
               const iterator& y) requires(random_access_range<maybe_const<Const, First>> &&
                                           (... &&
                                            random_access_range<maybe_const<Const, Views>>)) {
      return !(x < y);
    }

    // clang-format off
    constexpr friend auto
      operator<=>(const iterator& x,
                  const iterator& y) requires
      random_access_range<maybe_const<Const, First>> &&
      (... && random_access_range<maybe_const<Const, Views>>) && 
      three_way_comparable<maybe_const_iterator_t<Const, First>> &&
      (... && three_way_comparable<maybe_const_iterator_t<Const, Views>>) {
      return x.current_ <=> y.current_;
    }
    // clang-format on

    constexpr friend iterator
    operator+(const iterator& x, difference_type y) requires
      cartesian_is_random_access<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      return iterator{x} += y;
    }

    constexpr friend iterator
    operator+(difference_type x, const iterator& y) requires
      cartesian_is_random_access<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      return y + x;
    }

    constexpr friend iterator
    operator-(const iterator& x, difference_type y) requires
      cartesian_is_random_access<maybe_const<Const, First>, maybe_const<Const, Views>...> {
      return iterator{x} -= y;
    }

    constexpr friend difference_type
    operator-(const iterator& x, const iterator& y) requires(
      sized_sentinel_for<maybe_const_iterator_t<Const, First>,
                         maybe_const_iterator_t<Const, First>> &&
      (... &&
       sized_sentinel_for<maybe_const_iterator_t<Const, Views>,
                          maybe_const_iterator_t<Const, Views>>)) {
      return x.distance_to(y.current_);
    }

    constexpr friend difference_type
    operator-(iterator i,
              default_sentinel_t) requires cartesian_sentinel_is_sized<First, Views...> {
      auto end_tuple = [&]<size_t... Is>(index_sequence<Is...>) {
        return tuple(ranges::end(get<0>(i.parent_->bases_)),
                     ranges::begin(get<Is + 1>(i.parent_->bases_))...);
      }
      (index_sequence_for<Views...>{});
      return i.distance_to(end_tuple);
    }

    constexpr friend difference_type
    operator-(default_sentinel_t s,
              iterator i) requires cartesian_sentinel_is_sized<First, Views...> {
      return -(i - s);
    }

    friend constexpr auto
    iter_move(const iterator& i) noexcept(
      (noexcept(ranges::iter_move(declval<const maybe_const_iterator_t<Const, First>&>())) &&
       ...&& noexcept(ranges::iter_move(declval<const maybe_const_iterator_t<Const, Views>&>()))) &&
      (is_nothrow_move_constructible_v<maybe_const_rvalue_reference_t<Const, First>> && ... &&
       is_nothrow_move_constructible_v<maybe_const_rvalue_reference_t<Const, Views>>)) {
      return tuple_transform(ranges::iter_move, i.current_);
    }

    friend constexpr void
    iter_swap(const iterator& l,
              const iterator& r) noexcept(iter_tuple_swap_noexcept<Const, First, Views...>) requires
      iter_tuple_swappable<Const, First, Views...> {
      [&]<size_t... Is>(index_sequence<Is...>) {
        (ranges::iter_swap(get<Is>(l.current_), get<Is>(r.current_)), ...);
      }
      (index_sequence_for<First, Views...>{});
    }
  };

 public:
  cartesian_product_view() = default;
  constexpr explicit cartesian_product_view(First first_base, Views... bases)
    : bases_(std::move(first_base), std::move(bases)...) { }

  constexpr iterator<false>
  begin() requires(!simple_view<First> || ... || !simple_view<Views>) {
    return iterator<false>(*this, tuple_transform(ranges::begin, bases_));
  }

  constexpr iterator<true>
  begin() const requires((range<const First> && ... && range<const Views>)) {
    return iterator<true>(*this, tuple_transform(ranges::begin, bases_));
  }

  constexpr iterator<false>
    end() requires(!simple_view<First> || ... || !simple_view<Views>) &&
    cartesian_common_arg<First> {
    iterator<false> it(*this, tuple_transform(ranges::begin, bases_));
    get<0>(it.current_) = cartesian_common_arg_end(get<0>(bases_));
    return it;
  }

  constexpr iterator<true>
  end() const requires((cartesian_common_arg<const First> && ... && range<const Views>)) {
    iterator<true> it(*this, tuple_transform(ranges::begin, bases_));
    get<0>(it.current_) = cartesian_common_arg_end(get<0>(bases_));
    return it;
  }

  constexpr default_sentinel_t
  end() const requires(!cartesian_common_arg<const First> && ... && range<const Views>) {
    return default_sentinel;
  }

  constexpr auto
  size() requires cartesian_is_sized<First, Views...> {
    return apply([](auto&... base) { return (ranges::size(base) * ...); }, bases_);
  }

  constexpr auto
  size() const requires cartesian_is_sized<const First, const Views...> {
    return apply([](auto&... base) { return (ranges::size(base) * ...); }, bases_);
  }
};

template<class... Views>
cartesian_product_view(Views&&...) -> cartesian_product_view<views::all_t<Views>...>;

}  // namespace std::ranges

namespace std::ranges {

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

template<class C, input_range R, class... Args>
  requires(!view<C>)
constexpr C
to(R&& r, Args&&... args) {
  if constexpr (convertible_to<range_reference_t<R>, range_value_t<C>>) {
    if constexpr (constructible_from<C, R, Args...>)
      return C(std::forward<R>(r), std::forward<Args>(args)...);
    else if constexpr (common_range<R> && std::__detail::__cpp17_input_iterator<iterator_t<R>> &&
                       constructible_from<C, iterator_t<R>, sentinel_t<R>, Args...>)
      return C(ranges::begin(r), ranges::end(r), std::forward<Args>(args)...);
    else if constexpr (constructible_from<C, Args...> &&
                       container_insertable<C, range_reference_t<R>>) {
      C c(std::forward<Args>(args)...);
      if constexpr (sized_range<R> && reservable_container<C>)
        c.reserve(ranges::size(r));
      ranges::copy(r, container_inserter<range_reference_t<R>>(c));
      return c;
    }
  } else if (input_range<range_reference_t<R>>)
    return to<C>(r | views::transform([](auto&& elem) {
                   return to<range_value_t<C>>(std::forward<decltype(elem)>(elem));
                 }),
                 std::forward<Args>(args)...);
}

template<class R>
struct input_iter {
  using iterator_category = input_iterator_tag;
  using value_type = range_value_t<R>;
  using difference_type = ptrdiff_t;
  using pointer = add_pointer_t<range_reference_t<R>>;
  using reference = range_reference_t<R>;
  reference operator*() const;
  pointer operator->() const;
  input_iter& operator++();
  input_iter operator++(int);
  bool operator==(const input_iter&) const;
};

template<template<class...> class C, input_range R, class... Args>
constexpr auto
to(R&& r, Args&&... args) {
  if constexpr (requires { C(declval<R>(), declval<Args>()...); })
    return to<decltype(C(declval<R>(), declval<Args>()...))>(std::forward<R>(r),
                                                             std::forward<Args>(args)...);
  else if constexpr (requires {
                       C(declval<input_iter<R>>(), declval<input_iter<R>>(), declval<Args>()...);
                     })
    return to<decltype(C(declval<input_iter<R>>(), declval<input_iter<R>>(), declval<Args>()...))>(
      std::forward<R>(r), std::forward<Args>(args)...);
}

}  // namespace std::ranges

#endif
