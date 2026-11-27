// Sample the strict-walk last-return identity in length and verify the central corank band.
// See fourier-window.md for the error bounds. Build with -fno-fast-math -ffp-contract=off.
#include <algorithm>
#include <array>
#include <cfenv>
#include <cmath>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>

#ifdef __FAST_MATH__
#error "The certificate requires IEEE round-to-nearest arithmetic."
#endif
static_assert(std::numeric_limits<double>::is_iec559 && std::numeric_limits<double>::digits == 53);

using Fixed = __int128_t;
using Int = std::int64_t;
static_assert((Fixed(-1) >> 1) == -1, "fixed-point multiplication needs arithmetic right shift");
constexpr Fixed unit = Fixed(1) << 96;
constexpr Fixed pi96 = (Fixed(0x3243f6a88ULL) << 64) + 0x85a308d313198a2eULL;
constexpr double pi = 0x1.921fb54442d18p+1;
constexpr double roundoff = 0x1p-53;

void require(bool holds, const char* message) {
    if (!holds) throw std::runtime_error(message);
}

Fixed product(Fixed a, Fixed b) {
    constexpr Fixed mask = (Fixed(1) << 48)-1;
    Fixed h = a >> 48, k = b >> 48, l = a & mask, m = b & mask;
    return h*k + ((h*m + k*l + ((l*m) >> 48)) >> 48);
}

double as_double(Fixed value) { return static_cast<double>(value)*0x1p-96; }

struct Trig { Fixed cosine, sinc; };

Trig cos_sinc(Fixed angle) {
    static const auto coefficients = [] {
        std::array<Trig, 15> a{};
        a[0] = {unit, unit};
        for (int k = 1; k <= 14; ++k) {
            a[k] = {-a[k-1].cosine/((2*k)*(2*k-1)), -a[k-1].sinc/((2*k)*(2*k+1))};
        }
        return a;
    }();
    Fixed square = product(angle/2, angle/2);
    Trig v = coefficients[14];
    for (int k = 13; k >= 0; --k) {
        v = {coefficients[k].cosine + product(v.cosine, square),
             coefficients[k].sinc + product(v.sinc, square)};
    }
    return {2*product(v.cosine, v.cosine)-unit, product(v.cosine, v.sinc)};
}

struct Complex {
    double re = 0, im = 0;
    Complex operator+(Complex z) const { return {re+z.re, im+z.im}; }
    Complex operator-(Complex z) const { return {re-z.re, im-z.im}; }
    Complex operator*(Complex z) const { return {re*z.re-im*z.im, re*z.im+im*z.re}; }
};

class Fourier {
    std::vector<Complex> roots;
public:
    explicit Fourier(int size) : roots(size/2) {
        for (int k = 0; k < size/2; ++k) {
            int pos = std::min(k, size/2-k);
            Fixed angle = product(pi96, Fixed(2*pos)*(unit/size));
            Trig t = cos_sinc(angle);
            roots[k] = {as_double(k <= size/4 ? t.cosine : -t.cosine),
                        as_double(product(angle, t.sinc))};
        }
    }

    void apply(std::vector<Complex>& x, bool inverse = false) const {
        int n = static_cast<int>(x.size());
        require(n <= int(2*roots.size()) && (n & (n-1)) == 0, "FFT length out of range");
        for (int i = 1, j = 0; i < n; ++i) {
            int bit = n >> 1;
            for (; j & bit; bit >>= 1) j ^= bit;
            j ^= bit;
            if (i < j) std::swap(x[i], x[j]);
        }
        for (int length = 2; length <= n; length *= 2) {
            int stride = int(2*roots.size())/length;
            for (int start = 0; start < n; start += length) {
                for (int j = 0; j < length/2; ++j) {
                    Complex w = roots[stride*j];
                    if (inverse) w.im = -w.im;
                    Complex a = x[start+j], b = w*x[start+j+length/2];
                    x[start+j] = a+b;
                    x[start+j+length/2] = a-b;
                }
            }
        }
        if (inverse) for (auto& z : x) { z.re /= n; z.im /= n; }
    }
};

void kernel(int frequency, Int period, std::vector<Complex>& bridge, std::vector<Complex>& free) {
    Fixed omega = product(pi96, frequency*(unit/period));
    Fixed first = cos_sinc(omega).cosine, old_c = unit, old_s = unit;
    Fixed r = unit, p = unit, paired = unit;
    bridge[0].re = 1;
    free[0] = {1, as_double(first)};
    for (int j = 1; j < int(bridge.size()); ++j) {
        // Form the angle directly from its exact fraction of pi.
        Fixed angle = product(pi96, (Int(j)*frequency)*(unit/period));
        require(2*angle <= 3*unit, "kernel reached angle cutoff before certified truncation");
        auto [c, s] = cos_sinc(angle);
        Fixed odd = 2*product(c, old_c)-first;
        Fixed even = 2*product(c, c)-unit;
        Fixed abs_odd = odd < 0 ? -odd : odd;
        paired = product(paired, (unit+abs_odd)/2 + (Fixed(1)<<16)) + 1;
        if (paired < (unit >> 75)) break;
        Fixed inverse = static_cast<Fixed>((1/as_double(s))*0x1p96);
        inverse = product(inverse, 2*unit-product(inverse, s));
        Fixed defect = product(inverse, s)-unit;
        require(defect >= -(unit >> 81) && defect <= (unit >> 81), "sinc reciprocal");
        Fixed previous_ratio = product(old_s, inverse)*(j-1)/j;
        r = product(r, product(c, old_c+product(c, previous_ratio))/2);
        p = product(product(p, odd), even);
        bridge[j].re = as_double(r);
        free[j] = {as_double(p), as_double(product(p, 2*product(first, even)-odd))};
        old_c = c;
        old_s = s;
    }
}

int power_of_two(Int value) {
    int n = 1;
    while (n < value) n *= 2;
    return n;
}

std::vector<double> survivals(int last) {
    Fixed v = unit;
    std::vector<double> r(last+1, 1);
    for (int j = 1; j <= last; ++j) {
        v = v*(2*j-1)/(2*j);
        r[j] = as_double(v);
    }
    return r;
}

struct Samples { std::vector<Complex> phi; double residual; };

Samples solve(int frequency, Int period, int last, const std::vector<double>& r, const Fourier& fft,
              std::ostream* raw_sample = nullptr) {
    std::vector<Complex> bridge(last+1), free(last+1);
    kernel(frequency, period, bridge, free);
    // Newton inversion only proposes coefficients. A separate full linear convolution certifies them.
    int size = power_of_two(last+1);
    std::vector<Complex> recip(1, {1, 0});
    for (int k = 1; k < size; k *= 2) {
        std::vector<Complex> b(2*k), a = recip;
        a.resize(2*k);
        std::copy_n(bridge.begin(), std::min(2*k, last+1), b.begin());
        fft.apply(b); fft.apply(a);
        for (int i = 0; i < 2*k; ++i) b[i] = b[i]*a[i];
        fft.apply(b, true);
        for (int i = 0; i < k; ++i) b[i] = b[k+i];
        std::fill(b.begin()+k, b.end(), Complex{});
        fft.apply(b);
        for (int i = 0; i < 2*k; ++i) b[i] = b[i]*a[i];
        fft.apply(b, true);
        for (int i = 0; i < k; ++i) recip.push_back({-b[i].re, 0});
    }
    recip.resize(2*size);
    std::vector<Complex> candidate = free;
    candidate.resize(2*size);
    fft.apply(recip); fft.apply(candidate);
    for (int j = 0; j < 2*size; ++j) candidate[j] = candidate[j]*recip[j];
    fft.apply(candidate, true);
    candidate.resize(last+1);
    if (raw_sample) {
        // Hexadecimal floating-point output preserves the exact binary inputs.
        *raw_sample << std::hexfloat;
        for (int i = 0; i <= last; ++i)
            *raw_sample << bridge[i].re << ' ' << free[i].re << ' ' << free[i].im << ' '
                        << candidate[i].re << ' ' << candidate[i].im << '\n';
    }

    std::vector<Complex> check = candidate, b = bridge;
    check.resize(2*size); b.resize(2*size);
    fft.apply(b); fft.apply(check);
    for (int j = 0; j < 2*size; ++j) check[j] = b[j]*check[j];
    fft.apply(check, true);
    double err = 0, norm_r = 0, norm_u = 0;
    for (int j = 0; j <= last; ++j) {
        auto z = candidate[j];
        require(std::abs(z.re) <= 1.01*r[j] && std::abs(z.im) <= 1.01*r[j], "candidate magnitude");
        norm_r += bridge[j].re*bridge[j].re;
        norm_u += z.re*z.re + z.im*z.im;
        err = std::max({err, std::abs(check[j].re-free[j].re), std::abs(check[j].im-free[j].im)});
        candidate[j] = {z.re/r[j], z.im/r[j]};
    }
    int stages = 0;
    while ((1 << stages) < 2*size) ++stages;
    // FFT convolution, input kernels, conversion to binary64 and the residual subtraction.
    err = 1.00001*err + 60*stages*roundoff*(std::sqrt(norm_r*norm_u)+.001) + 0x1p-47;
    return {std::move(candidate), err};
}

Int scale_floor(int index) {
    Int v = 2LL*index, cube = v*v*v;
    Int s = static_cast<Int>(std::sqrt(double(cube)));
    while (s*s > cube) --s;
    while ((s+1)*(s+1) <= cube) ++s;
    return s;
}

struct Group {
    int first, last, stop;
    Int scale;
    std::vector<Complex> left, right;
    double error[2][2] = {};
    Group(int a, int b, Int period) : first(a), last(b), scale(scale_floor(a)) {
        stop = int((204800*period+628*scale-1)/(628*scale));
        left.resize(stop+1);
        right.resize(stop+1);
    }

    void add(int freq, Int period, const Samples& sample, double survival) {
        left[freq] = sample.phi[first];
        right[freq] = sample.phi[last];
        double delta[2] = {};
        for (int n = first; n <= last; ++n) {
            double v = double(n-first)/std::max(1, last-first);
            double a = (1-v)*left[freq].re + v*right[freq].re;
            double b = (1-v)*left[freq].im + v*right[freq].im;
            delta[0] = std::max(delta[0], std::abs(sample.phi[n].re-a));
            delta[1] = std::max(delta[1], std::abs(sample.phi[n].im-b));
        }
        double xi = 2*pi*freq*scale/period;
        for (int parity = 0; parity < 2; ++parity) {
            double cost = 4.*scale/period*(delta[parity]+2.0001*sample.residual/survival+1e-14);
            error[parity][0] += xi*cost;
            error[parity][1] += xi*xi*cost;
        }
    }
};

std::array<double, 3> certify_curve(const Group& g, const std::vector<Complex>& sample,
                                    int parity, Int period, const Fourier& fft) {
    constexpr int mesh = 32768;
    double dx = double(period)/(mesh*double(g.scale));
    std::array<double, 3> margins{1e30, 1e30, 1e30};
    for (int order : {1, 2}) {
        std::vector<Complex> table(mesh);
        double norm = 0, curvature = 0;
        for (int j = 1; j <= g.stop; ++j) {
            double xi = 2*pi*j*g.scale/period;
            double c = 4.*g.scale/period*(parity ? sample[j].im : sample[j].re)*xi;
            if (order == 2) c *= xi;
            table[j] = order == 1 ? Complex{0, c} : Complex{-c, 0};
            norm += std::abs(c);
            curvature += std::abs(c)*xi*xi;
        }
        require(norm < 1e6 && g.stop < mesh/2, "spatial interpolation norm");
        fft.apply(table);
        double reserve = (order == 1 ? .00026 : .95) + .00001
                       + 1.00001*(g.error[parity][order-1] + dx*dx*curvature/8);
        for (int k = 0; k < mesh; ++k) {
            double x = k*dx;
            if (order == 1 && x+dx >= .13589 && x-dx <= .33901)
                margins[0] = std::min(margins[0], table[k].re-reserve);
            if (order == 2 && x+dx >= .33299 && x-dx <= .40401)
                margins[1] = std::min(margins[1], -table[k].re-reserve);
            if (order == 1 && x+dx >= .39799 && x-dx <= .63101)
                margins[2] = std::min(margins[2], -table[k].re-reserve);
        }
    }
    return margins;
}

void verify_range(int first, int last) {
    require(first >= 2049 && last <= 300000 && first <= last, "require 2049 <= first <= last <= 300000");
    require(std::fegetround() == FE_TONEAREST, "rounding mode");
    auto r = survivals(last);
    Fourier fft(std::max(32768, 2*power_of_two(last+1)));
    while (first <= last) {
        Int period = 1;
        while (period < 5*(scale_floor(first)+1)) period *= 2;
        int end = first;
        while (end < last && 5*(scale_floor(end+1)+1) <= period) ++end;
        std::vector<Group> groups;
        for (int a = first; a <= end;) {
            int b = std::min(end, a+a/100);
            groups.emplace_back(a, b, period);
            a = b+1;
        }
        for (int f = 1; f <= groups.front().stop; ++f) {
            int need = 0;
            for (auto& g : groups) if (f <= g.stop) need = g.last;
            auto samples = solve(f, period, need, r, fft);
            for (auto& g : groups) if (f <= g.stop) g.add(f, period, samples, r[g.last]);
        }
        std::array<double, 3> worst{1e30, 1e30, 1e30};
        for (auto& g : groups) {
            for (const auto* sample : {&g.left, &g.right}) {
                for (int parity : {0, 1}) {
                    auto margins = certify_curve(g, *sample, parity, period, fft);
                    for (int i = 0; i < 3; ++i) worst[i] = std::min(worst[i], margins[i]);
                    if (*std::min_element(margins.begin(), margins.end()) <= 0) {
                        std::cerr << "Uncertified N=" << g.first << ".." << g.last
                                  << " strict parity=" << parity << " margins "
                                  << margins[0] << ' ' << margins[1] << ' ' << margins[2]
                                  << " transform errors " << g.error[parity][0] << ' '
                                  << g.error[parity][1] << '\n';
                        throw std::runtime_error("central sign test");
                    }
                }
            }
        }
        std::cout << "Certified strict half-lengths N=" << first << ".." << end
                  << " in both parities. Margins " << worst[0] << ' ' << worst[1] << ' '
                  << worst[2] << std::endl;
        first = end+1;
    }
}

double cosine_pi(Int numerator, Int denominator) {
    Int tick = numerator % (2*denominator);
    tick = std::min(tick, 2*denominator-tick);
    bool negative = 2*tick > denominator;
    if (negative) tick = denominator-tick;
    Fixed angle = product(pi96, tick*(unit/denominator));
    Fixed c = cos_sinc(angle).cosine;
    return as_double(negative ? -c : c);
}

void test_small() {
    constexpr int last = 13;
    const auto r = survivals(last);
    Fourier fft(1024);
    std::vector<std::vector<int>> counts(26);
    for (int m = 2; m <= 25; ++m) {
        int degree = m*m/4;
        counts[m].resize(degree+1);
        std::function<void(int,int,int)> visit = [&](int row, int previous, int rank) {
            ++counts[m][degree-rank];
            for (int p = 1; p < previous && p <= m-1-2*row; ++p) visit(row+1, p, rank+p);
        };
        visit(0, m, 0);
    }
    for (int f : {1, 2, 5, 7, 9}) {
        Int period = 256;
        auto samples = solve(f, period, last, r, fft);
        for (int m = 2; m <= 25; ++m) {
            int n = (m+1)/2, twice_d = m+1+n;
            double mass = 0, total = 0;
            for (int k = 0; k < int(counts[m].size()); ++k) {
                mass += counts[m][k]*cosine_pi((2*k+twice_d)*f, period);
                total += counts[m][k];
            }
            double estimated = m%2 ? samples.phi[n].re : samples.phi[n].im;
            require(std::abs(estimated-mass/total) < 2.0001*samples.residual/r[n]+1e-14,
                    "direct signed area comparison");
        }
    }
    // Full inversion from directly enumerated signed samples, including the single Nyquist term.
    constexpr int q = 512;
    for (int m = 2; m <= 25; ++m) {
        int twice_d = m+1+(m+1)/2;
        std::vector<double> cf(q/2+1);
        for (int j = 0; j <= q/2; ++j) {
            for (int k = 0; k < int(counts[m].size()); ++k)
                cf[j] += counts[m][k]*cosine_pi((2*k+twice_d)*j, q);
        }
        for (int k = 0; k < int(counts[m].size()); ++k) {
            double y = cf[0]+cf[q/2]*cosine_pi((2*k+twice_d)*(q/2), q);
            for (int j = 1; j < q/2; ++j)
                y += 2*cf[j]*cosine_pi((2*k+twice_d)*j, q);
            require(std::abs(2*y/q-counts[m][k]) < 1e-7, "direct Fourier coefficient inversion");
        }
    }
    std::cout << "Signed kernels and every inverted coefficient agree with direct enumeration "
                 "for both families through n=12.\n";
}

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--self-test") { test_small(); return 0; }
        if (argc == 5 && std::string(argv[1]) == "--residual-inputs") {
            int last = std::stoi(argv[2]);
            Int period = std::stoll(argv[3]);
            int frequency = std::stoi(argv[4]);
            require(1 <= last && last <= 300000, "invalid half-length");
            require(2 <= period && period <= (Int(1) << 32) && (period & (period-1)) == 0,
                    "invalid period");
            require(1 <= frequency && frequency <= period/2, "invalid frequency");
            require(std::fegetround() == FE_TONEAREST, "rounding mode");
            Fourier fft(std::max(32768, 2*power_of_two(last+1)));
            solve(frequency, period, last, survivals(last), fft, &std::cout);
            return 0;
        }
        require(argc == 3, "usage: verify_fourier_window first_N last_N | --self-test | "
                           "--residual-inputs last_N period frequency");
        verify_range(std::stoi(argv[1]), std::stoi(argv[2]));
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
