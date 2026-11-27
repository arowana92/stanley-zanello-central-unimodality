// Certify upper-half strict log-concavity using the window in rising-window.md.
// certified-window.md proves the relative error bound for the arithmetic below.
#include <algorithm>
#include <cfenv>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef __FAST_MATH__
#error "Use IEEE arithmetic without fast-math"
#endif
static_assert(std::numeric_limits<double>::is_iec559 &&
              std::numeric_limits<double>::digits == 53 &&
              std::numeric_limits<double>::radix == 2);

int window_end(int length) {
    const std::int64_t squared = 4LL * length * length * length;
    std::int64_t k = static_cast<std::int64_t>(std::sqrt(static_cast<double>(squared)));
    while (k*k > squared) --k;
    while ((k+1)*(k+1) <= squared) ++k;
    return static_cast<int>(k);
}

int min_area(int height) {
    return height * height / 4;
}

void enumerate(int length, int row, int previous, int rank,
               std::vector<std::uint64_t>& ranks) {
    ++ranks[rank];
    const int largest = std::min(previous-1, length-1-2*row);
    for (int part = 1; part <= largest; ++part) {
        enumerate(length, row+1, part, rank+part, ranks);
    }
}

template<class Number>
void check_direct(int length, const std::vector<Number>& row, Number unit) {
    const int degree = length*length/4;
    std::vector<std::uint64_t> ranks(degree+1, 0);
    enumerate(length, 0, length, 0, ranks);
    for (int k = 0; k <= degree; ++k) {
        if (static_cast<double>(row[k]) != static_cast<double>(unit) * ranks[degree-k]) {
            throw std::runtime_error("direct count differs at length " + std::to_string(length));
        }
    }
    const auto peak = std::max_element(ranks.begin(), ranks.end());
    if (!std::is_sorted(ranks.begin(), peak+1) ||
        !std::is_sorted(peak, ranks.end(), std::greater<std::uint64_t>())) {
        throw std::runtime_error("direct row is not unimodal at length " + std::to_string(length));
    }
}

template<bool scale_blocks = false, class Number, class WindowEnd, class Check>
void visit_window(int max_n, int cap, Number unit, WindowEnd window, Check check) {
    const int last = 2*max_n+1;
    std::vector<std::vector<Number>> heights;
    for (int h = 0; h <= last && min_area(h) <= cap; ++h) {
        heights.emplace_back(cap-min_area(h)+1, Number{});
    }
    heights[0][0] = unit;
    const int highest = static_cast<int>(heights.size())-1;
    for (int t = 1; t <= last; ++t) {
        const int degree = t*t/4;
        // Each height reads only the opposite parity, still at time t-1.
        for (int h = t%2; h <= std::min(t, highest); h += 2) {
            const int downs = (t-h)/2;
            const int end = std::min(cap, degree-downs*(downs+1)/2)-min_area(h)+1;
            auto& dest = heights[h];
            const int shift = std::min(h, end);
            if (h == 0) {
                std::copy_n(heights[1].begin(), end, dest.begin());
            } else if (h == highest) {
                std::copy_n(heights[h-1].begin(), end, dest.begin());
            } else {
                const auto& up = heights[h-1];
                const auto& down = heights[h+1];
                std::copy_n(up.begin(), shift, dest.begin());
                for (int i = shift; i < end; ++i) dest[i] = up[i] + down[i-h];
            }
            if constexpr (scale_blocks) {
                if (t % 256 == 0) {
                    for (int i = 0; i < end; ++i) dest[i] *= 0x1p-256;
                }
            }
        }
        if (t < 2) continue;
        const int stop = std::min(degree/2, window(t));
        const int last_corank = (t <= 25) ? degree : stop+1;
        std::vector<Number> row(last_corank+1);
        for (int h = t%2; h <= std::min(t, highest); h += 2) {
            const int first = min_area(h);
            for (int k = first; k <= last_corank; ++k) row[k] = row[k] + heights[h][k-first];
        }
        if (t <= 25) check_direct(t, row, unit);
        if (t/2 >= 9) check(t, stop, row);
    }
}

void check_ratios(int t, int first, int stop, const std::vector<double>& row, double factor) {
    double left = row[first]/row[first-1];
    for (int k = first; k <= stop; ++k) {
        const double right = row[k+1]/row[k];
        if (!std::isnormal(left) || !std::isnormal(right) || !(left > right*factor)) {
            throw std::runtime_error("uncertified ratio at length " + std::to_string(t) +
                                     ", corank " + std::to_string(k));
        }
        left = right;
    }
}

void certify(int max_n) {
    if (std::fegetround() != FE_TONEAREST) throw std::runtime_error("rounding mode");
    if (max_n < 12 || max_n > 1019) throw std::invalid_argument("require 12 <= max_n <= 1019");
    const int cap = std::max(25*25/4, window_end(2*max_n+1)+1);
    std::int64_t checked = 0;
    visit_window(max_n, cap, std::ldexp(1.0, -max_n), window_end,
                 [&](int t, int stop, const std::vector<double>& row) {
        check_ratios(t, 1, stop, row, 1.0+0x1p-36);
        checked += stop;
        if (t % 256 == 0) std::cout << "Verified through word length " << t << std::endl;
    });
    std::cout << "Certified " << checked << " strict determinants in both families for 9 <= n <= "
              << max_n << ". Direct counts agree through n = 12." << std::endl;
}

void certify_scaled(int max_n) {
    if (std::fegetround() != FE_TONEAREST) throw std::runtime_error("rounding mode");
    if (max_n < 12 || max_n > 2048) throw std::invalid_argument("require 12 <= max_n <= 2048");
    const int cap = std::max(25*25/4, window_end(2*max_n+1)+1);
    const int first = 4097;  // The --tail 4096 certificate covers smaller coranks.
    std::int64_t checked = 0;
    visit_window<true>(max_n, cap, 1.0, window_end,
                       [&](int t, int stop, const std::vector<double>& row) {
        if (stop < first) return;
        const double floor = std::ldexp(1.0, t%256-920);
        for (int k = first-1; k <= stop+1; ++k) {
            if (!(row[k] >= floor && std::isfinite(row[k]))) {
                throw std::runtime_error("insufficient mass at length " + std::to_string(t) +
                                         ", corank " + std::to_string(k));
            }
        }
        check_ratios(t, first, stop, row, 1.0+0x1p-35);
        checked += stop-first+1;
        if (t % 512 == 0) std::cout << "Verified through word length " << t << std::endl;
    });
    std::cout << "Certified " << checked << " strict determinants above corank 4096 through n="
              << max_n << ". Direct counts agree through n=12." << std::endl;
}

// Nonnegative counts rounded down to 48 significant binary digits.
// A positive value represents mantissa * 2^(exponent-47).
struct Count {
    std::uint64_t mantissa = 0;
    int exponent = -48;

    explicit operator double() const {
        return std::ldexp(static_cast<double>(mantissa), exponent-47);
    }
};

Count operator+(Count left, Count right) {
    if (left.exponent < right.exponent) std::swap(left, right);
    const int shift = left.exponent - right.exponent;
    if (shift >= 48) return left;
    left.mantissa += right.mantissa >> shift;
    if (left.mantissa >= (1ULL << 48)) {
        left.mantissa >>= 1;
        ++left.exponent;
    }
    return left;
}

// Verify (scale-loss) * center^2 > scale * left * right, with a
// relative reserve of 2^-27 on the right to cover all downward rounding.
bool separated(Count left, Count center, Count right, int scale, int loss) {
    if (!left.mantissa || !center.mantissa || !right.mantissa) return false;
    const int shift = 2*center.exponent-left.exponent-right.exponent;
    using Product = unsigned __int128;
    Product lhs = Product(scale-loss) * center.mantissa * center.mantissa;
    Product rhs = Product(scale) * left.mantissa * right.mantissa;
    rhs += (rhs >> 27) + 1;
    // For normalized mantissas their squared/product ratio is in (1/4,4).
    if (shift >= 4) return true;
    if (shift <= -4) return false;
    if (shift >= 0) lhs <<= shift;
    else rhs <<= -shift;
    return lhs > rhs;
}

void certify_tail(int limit) {
    if (limit < 12 || limit > 4096) throw std::invalid_argument("require 12 <= corank <= 4096");
    const int cap = std::max(25*25/4, limit+1);
    std::int64_t strict = 0, quantitative = 0;
    visit_window(3*limit, cap, Count{1ULL << 47, 0}, [=](int) { return limit; },
                 [&](int t, int stop, const std::vector<Count>& row) {
        const int n = t/2;
        for (int k = n/3+1; k <= stop; ++k) {
            const bool margin = k <= 2*n;
            if (!separated(row[k-1], row[k], row[k+1], margin ? 40*k : 1, margin ? 1 : 0)) {
                throw std::runtime_error("uncertified tail at length " + std::to_string(t) +
                                         ", corank " + std::to_string(k));
            }
            ++strict;
            if (margin) ++quantitative;
        }
    });
    std::cout << "Certified " << strict << " strict determinants, including " << quantitative
              << " relative margins, through corank " << limit << " and n=" << 3*limit
              << ". Direct counts agree through n=12." << std::endl;
}

int main(int argc, char** argv) {
    try {
        if (argc == 3 && std::string(argv[1]) == "--tail") certify_tail(std::stoi(argv[2]));
        else if (argc == 3 && std::string(argv[1]) == "--scaled") certify_scaled(std::stoi(argv[2]));
        else if (argc <= 2) certify(argc == 2 ? std::stoi(argv[1]) : 1000);
        else throw std::invalid_argument("usage: verify_window [max_n] | --tail corank | --scaled max_n");
    } catch (const std::exception& error) {
        std::cerr << error.what() << std::endl;
        return 1;
    }
}
