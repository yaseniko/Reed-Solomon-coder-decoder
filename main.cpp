#include <algorithm>
#include <bitset>
#include <ctime>
#include <iostream>
#include <memory>
#include <numeric>
#include <vector>

constexpr int gf_size = 256;
constexpr int nonzero_size = gf_size - 1;
constexpr int prime_polynom = 285; // y^8 + y^4 + y^3 + y^2 + 1
constexpr int alpha = 2;

static std::vector<size_t> logs_table (gf_size);
static std::vector<size_t> exponents_table (2 * nonzero_size);


//-------------------------------Galois Arithmetics---------------------------------

namespace GF
{
  size_t add (size_t x, size_t y)
  {
    return x ^ y;
  }

  size_t mult (size_t x, size_t y)
  {
    return (x == 0 || y == 0) ? 0 : exponents_table[logs_table[x] + logs_table[y]];
  }

  size_t div (size_t x, size_t y)
  {
    if (y == 0)
      throw -4;

    if (x == 0)
      return 0;

    return exponents_table[logs_table[x] - logs_table[y] + nonzero_size];
  }

  size_t pow (size_t x, size_t pow)
  {
    size_t index = (logs_table[x] * pow) % nonzero_size;

    return exponents_table[index];
  }

  size_t inverse(size_t x)
  {
    return exponents_table[nonzero_size - logs_table[x]];
  }
};


//---------------------------------Polynomial Manipulations---------------------------------

class polynom
{
public:
  size_t deg = 0;

private:
  std::vector<size_t> coeffs;

public:
  polynom () = delete;

  polynom (size_t deg_arg) : deg (deg_arg)
  {
    coeffs.assign (deg + 1, 0);
  }

  polynom (size_t deg_arg, size_t value) : deg (deg_arg)
  {
    coeffs.resize (deg + 1, value);
  }

  polynom (const polynom &p) : deg (p.deg)
  {
    coeffs.resize (deg + 1);

    for (size_t i = 0; i <= deg; i++)
      coeffs[i] = p[i];
  }

  polynom (std::string str) : deg (str.size () - 1)
  {
    coeffs.resize (deg + 1);

    for (size_t i = 0; i <= deg; i++)
      coeffs[i] = static_cast<size_t> (str[i]);
  }

  polynom (const polynom &p, const polynom &q) : deg (p.deg + q.deg + 1)
  {
    coeffs.resize (deg + 1);

    for (size_t i = 0; i <= p.deg; i++)
      coeffs[i] = p[i];

    for (size_t i = p.deg + 1; i <= deg; i++)
      coeffs[i] = q[i - p.deg - 1];
  }

  void create_random (size_t deg_arg)
  {
    deg = deg_arg - 1;
    coeffs.resize (deg_arg);

    srand (static_cast<unsigned int> (time (nullptr)));
    std::for_each (coeffs.begin (), coeffs.end (), [&] (size_t &elem) { elem = rand () % gf_size; });
  }

  void reverse ()
  {
    for (size_t i = 0; i < (deg + 1) / 2; i++)
      std::swap (coeffs[i], coeffs[deg - i]);
  }

  void clear ()
  {
    coeffs.assign (deg + 1, 0);
  }

  void limit (size_t deg_arg)
  {
    coeffs.resize (deg_arg + 1);
    deg = deg_arg;
  }

  void add_elem (size_t elem)
  {
    deg++;
    coeffs.resize (deg + 1);

    for (size_t i = deg; i > 0; i--)
      coeffs[i] = coeffs[i - 1];
    coeffs[0] = elem;
  }

  void delete_leading_zeroes ()
  {
    while (coeffs[deg] == 0)
      deg--;

    coeffs.resize (deg + 1);
  }

  polynom operator= (const polynom &p)
  {
    if (this == &p)
      return *this;

    deg = p.deg;
    coeffs.resize (deg + 1);
    for (size_t i = 0; i <= deg; i++)
      coeffs[i] = p[i];

    return *this;
  }

  size_t& operator[] (const size_t ind)
  {
    return coeffs[ind];
  }

  size_t operator[] (const size_t ind) const
  {
    return coeffs[ind];
  }

  void print () const
  {
    std::for_each (coeffs.begin (), coeffs.end (), [&] (const size_t &elem) { printf ("%lu ", elem); });
    printf ("\n");
  }

  void print_binary () const
  {
    std::for_each (coeffs.begin (), coeffs.end (), [&] (const size_t &elem) { std::cout << std::bitset<8> (elem); });
    printf ("\n");
  }

  void print_message () const
  {
    std::for_each (coeffs.begin (), coeffs.end (), [&] (const size_t &elem) { printf ("%c", static_cast<char> (elem)); });
    printf ("\n");
  }

  size_t evaluate (size_t x) const
  {
    polynom p_r = *this;
    p_r.reverse ();

    size_t y = p_r[0];
    for (size_t i = 1; i <= p_r.deg; i++)
      y = GF::mult (y, x) ^ p_r[i];

    return y;
  }
};

namespace GF_POLYNOM
{
  polynom add (const polynom &p, const polynom &q)
  {
    polynom res (std::max (p.deg, q.deg));

    for (size_t i = 0; i <= p.deg; i++)
      res[i] = p[i];

    for (size_t i = 0; i <= q.deg; i++)
      res[i] ^= q[i];

    return res;
  }

  polynom mult (const polynom &p, const polynom &q)
  {
    polynom res (p.deg + q.deg);

    for (size_t i = 0; i <= p.deg; i++)
      for (size_t j = 0; j <= q.deg; j++)
        res[i + j] ^= GF::mult (p[i], q[j]);

    return res;
  }

  polynom rem (const polynom &p, const polynom &q)
  {
    polynom p_r = p, q_r = q;
    p_r.reverse (); q_r.reverse ();

    for (size_t i = 0; i <= p_r.deg - q_r.deg; i++)
      {
        size_t coeff = p_r[i];
        if (coeff != 0)
          for (size_t j = 1; j <= q_r.deg; j++)
            if (q_r[j] != 0)
              p_r[i + j] ^= GF::mult (q_r[j], coeff);
      }

    p_r.reverse ();
    p_r.limit (q.deg - 1);
    return p_r;
  }

  polynom scale (const polynom &p, size_t x)
  {
    polynom res (p.deg);

    for (size_t i = 0; i <= p.deg; i++)
      res[i] = GF::mult (p[i], x);

    return res;
  }
};

//--------------------------------------Encode staff-----------------------------------------

polynom encode (const polynom &message_to_code, const polynom &gen)
{
  polynom zero (gen.deg - 1);
  polynom rem = GF_POLYNOM::rem (polynom (zero, message_to_code), gen);

#if 0
  message_to_code.print ();
  gen.print ();
  rem.print ();
#endif

  return polynom (rem, message_to_code);
}

polynom corrupt_message (const polynom &message_to_corrupt, size_t err_num)
{
  srand (static_cast<unsigned int> (time (nullptr)));

  std::vector<size_t> corrupted_positions (message_to_corrupt.deg + 1);
  corrupted_positions[0] = 0;
  std::iota (corrupted_positions.begin () + 1, corrupted_positions.end (), 1);
  std::random_shuffle (corrupted_positions.begin (), corrupted_positions.end (), [&] (int) { return rand () % message_to_corrupt.deg; });
  std::sort (corrupted_positions.begin (), corrupted_positions.begin () + err_num);

  polynom corrupted_message = message_to_corrupt;
  for (size_t i = 0; i < err_num; i++)
    corrupted_message[corrupted_positions[i]] ^= (rand () % nonzero_size + 1);

#if 1
  std::cout << "Corrupted positions:\n";
  for (size_t i = 0; i < err_num; i++)
    std::cout << corrupted_positions[i] << " ";
  std::cout << std::endl;
#endif

  return corrupted_message;
}

//--------------------------------------Decode staff-----------------------------------------

polynom calc_syndromes (const polynom &message, size_t syndrom_deg)
{
  polynom syndrom (syndrom_deg);

  for (size_t i = 0; i <= syndrom_deg; i++)
    syndrom[i] = message.evaluate (GF::pow (alpha, i));

  return syndrom;
}

bool is_syndrom_zero (const polynom &syndrom)
{
  for (size_t i = 0; i <= syndrom.deg; i++)
    if (syndrom[i] != 0)
      return false;

  return true;
}

polynom BM_find_locators (const polynom &syndroms, size_t symbols)
{
  polynom r_syndroms = syndroms;
  r_syndroms.reverse ();

  polynom locators (0), old_locators (0);
  locators[0] = old_locators[0] = 1;

  for (size_t i = 0; i < symbols; i++)
    {
      size_t delta = r_syndroms[i];
      for (size_t j = 1; j <= locators.deg; j++)
        delta ^= GF::mult (locators[j], r_syndroms[i - j]);

      old_locators.add_elem (0);

      if (delta != 0)
        {
          if (old_locators.deg > locators.deg)
            {
              polynom new_locators = GF_POLYNOM::scale (old_locators, delta);
              old_locators = GF_POLYNOM::scale (locators, GF::inverse (delta));
              locators = new_locators;
            }

          polynom tmp = GF_POLYNOM::add (locators, GF_POLYNOM::scale (old_locators, delta));
          locators = tmp;
        }
    }

  locators.delete_leading_zeroes ();
  if (2 * locators.deg > symbols)
    throw -1;

  return locators;
}

std::vector<size_t> find_error_positions (const polynom &locators, size_t message_len)
{
  std::vector<size_t> err_positions;
  size_t errs_total = locators.deg, errs_founded = 0;

  for (size_t i = 0; i < message_len; i++)
    {
      if (locators.evaluate (GF::pow (alpha, i)) == 0)
        {
          err_positions.push_back (i);
          errs_founded++;
        }
    }

  if (errs_founded != errs_total)
    throw -2;

  return err_positions;
}

polynom find_locator_polynom (const std::vector<size_t> &pos)
{
  polynom e_loc (0);
  e_loc[0] = 1;

  for (auto i : pos)
    {
      polynom p (1); p[0] = 1; p[1] = GF::pow (alpha, i);
      e_loc = GF_POLYNOM::mult (e_loc, p);
    }

  return e_loc;
}

polynom find_omega_polynom (const polynom &syndrom, const polynom &err_loc)
{
  polynom p (err_loc.deg + 1);
  p[p.deg] = 1;

  polynom omega = GF_POLYNOM::mult (syndrom, err_loc);
  return GF_POLYNOM::rem (omega, p);
}

polynom forney_correct_errors (const polynom &msg, const polynom &syndrom, const std::vector<size_t> &err_pos)
{
  polynom locators = find_locator_polynom (err_pos);
  polynom omega = find_omega_polynom (syndrom, locators);

  std::vector<size_t> err_pos_exps;
  for (auto err : err_pos)
    err_pos_exps.push_back (GF::pow (alpha, err));

  polynom err_values (msg.deg);
  for (size_t i = 0; i < err_pos_exps.size (); i++)
    {
      size_t x_inv = GF::inverse (err_pos_exps[i]);

      size_t loc_deriv_value = 1;
      for (size_t j = 0; j < err_pos_exps.size (); j++)
        if (j != i)
          loc_deriv_value = GF::mult (loc_deriv_value, GF::add (1, GF::mult (x_inv, err_pos_exps[j])));

      if (loc_deriv_value == 0)
        throw -3;

      size_t omega_value = omega.evaluate (x_inv);
      size_t err_value = GF::div (omega_value, loc_deriv_value);
      err_values[err_pos[i]] = err_value;
    }

  polynom res = GF_POLYNOM::add (msg, err_values);
  return res;
}

polynom decode (const polynom &message_to_decode, size_t doubled_errors)
{
  polynom syndromes = calc_syndromes (message_to_decode, doubled_errors - 1);
  if (is_syndrom_zero (syndromes))
    {
      polynom res = message_to_decode;
      res.reverse ();
      res.limit (message_to_decode.deg - doubled_errors);
      res.reverse ();
      return res;
    }

  if (message_to_decode.deg >= gf_size)
    {
      std::cout << "Message is too long. Can't decode\n";
      exit (-1);
    }

  auto handle_exception = [] (int err)
  {
    switch (err)
      {
      case -1:
      case -2:
        std::cerr << "Too many errors to decode\n";
        break;
      case -3:
        std::cerr << "Problems with finding value of error. Can't decode\n";
        break;
      case -4:
        std::cerr << "Zero division error\n";
        break;
      default:
        std::cerr << "Unknown error\n";
      }
  };

  polynom decoded_message (0);

  try
  {
    polynom locators = BM_find_locators (syndromes, doubled_errors);
    std::vector<size_t> err_positions = find_error_positions (locators, message_to_decode.deg + 1);
    decoded_message = forney_correct_errors (message_to_decode, syndromes, err_positions);
  }
  catch (int err)
  {
    handle_exception (err);
    exit (-1);
  }

#if 0
  syndromes = calc_syndromes (decoded_message, doubled_errors - 1);
  if (is_syndrom_zero (syndromes))
    std::cout << "Zero syndromes. Successful decoding\n";
  else
    std::cout << "Nonzero syndromes. Unsuccessful decoding\n";

  printf ("Locators:\n");
  locators.print ();

  printf ("Positions:\n");
  for (size_t i = 0; i < err_pos.size (); i++)
    printf ("%lu ", err_positions[i]);
  printf ("\n");
#endif

  decoded_message.reverse ();
  decoded_message.limit (message_to_decode.deg - doubled_errors);
  decoded_message.reverse ();
  return decoded_message;
}


//--------------------------------------Other Staff------------------------------------------

void print_logs_table ()
{
  printf ("LOGS TABLE:\n");

  for (size_t i = 0; i < nonzero_size; i++)
    printf ("%lu ", logs_table[i]);

  printf ("\n\n");
}


void print_exponents_table ()
{
  printf ("EXP TABLE:\n");

  for (size_t i = 0; i < nonzero_size; i++)
    printf ("%lu ", exponents_table[i]);

  printf ("\n\n");
}

void init_tables ()
{
  size_t x = 1;
  for (size_t i = 0; i < nonzero_size; i++)
    {
      exponents_table[i] = x;
      logs_table[x] = i;

      x <<= 1;
      if (x >= gf_size)
        x ^= prime_polynom;
    }

#if 0
  print_logs_table ();
  print_exponents_table ();
#endif

  std::copy_n (exponents_table.data (), nonzero_size, exponents_table.data () + nonzero_size);
}

polynom init_generator (size_t deg)
{
  polynom res (0); res[0] = 1;

  for (size_t i = 0; i < deg; i++)
    {
      polynom p (1);
      p[1] = 1; p[0] = GF::pow (alpha, i);

      res = GF_POLYNOM::mult (res, p);
    }

  return res;
}


int main (int argc, char **argv)
{
  if (argc != 4)
    {
      printf ("usage: %s <len of message> <max errors for decoder> <num errors to random>\n", argv[0]);
      return -1;
    }

#if 0
  polynom message (10, 100);
#else
  polynom message (0);
  message.create_random (atoi (argv[1]));
#endif

  size_t n_err = static_cast<size_t> (atoi (argv[2]));

  init_tables ();
  polynom gen = init_generator (2 * n_err);

  std::cout << "Original message:\n";
  message.print ();
  // message.print_binary ();
  // message.print_message ();

  polynom coded_message = encode (message, gen);
  std::cout << "Encoded message:\n";
  coded_message.print ();
  // coded_message.print_binary ();
  // coded_message.print_message ();

  polynom corrupted_message = corrupt_message (coded_message, atoi (argv[3]));
  std::cout << "Corrupted message:\n";
  corrupted_message.print ();
  // corrupted_message.print_binary ();
  // corrupted_message.print_message ();

  polynom decoded_message = decode (corrupted_message, 2 * n_err);
  std::cout << "Decoded message:\n";
  decoded_message.print ();
  // decoded_message.print_binary ();
  // decoded_message.print_message ();

  return 0;
}

