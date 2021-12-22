/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"


#include <vector>

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:
  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
    {
      return true;
    }
    if ( try_distributivity( n ) )
    {
      return true;
    }
    if ( try_3_layer_distributivity( n ) )
    {
      return true;
    }

    return false;
  }

  void modify_associativity (signal a, signal b, signal c, node n)
  {
    signal g1 = ntk.create_and (a, b) ;
    signal g0 = ntk.create_and (c, g1) ;
    ntk.substitute_node (n, g0) ;
    //ntk.update_levels () ;
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    std::vector <signal> fanin ;
    ntk.foreach_fanin (n, [&](auto const& fi) {
      fanin.push_back (fi) ;
    }) ;

    if (ntk.is_pi (ntk.get_node (fanin [0])) && ntk.is_pi (ntk.get_node (fanin [1])))
    {
      return false ;
    }
    if  (ntk.is_on_critical_path (n))
    {
      node g0 = ntk.get_node (fanin [0]) ;
      node g1 = ntk.get_node (fanin [1]) ;

      std::vector <signal> g0_fi ;
      ntk.foreach_fanin (g0, [&](auto const& fi) {
        g0_fi.push_back (fi) ;
      }) ;

      std::vector <signal> g1_fi ;
      ntk.foreach_fanin (g1, [&](auto const& fi) {
        g1_fi.push_back (fi) ;
      }) ;

      if (ntk.level (g1) > ntk.level (g0) + 1 && !ntk.is_complemented (fanin [1]))
      {
        if (ntk.is_on_critical_path (ntk.get_node (g1_fi [0])) && ntk.is_on_critical_path (ntk.get_node (g1_fi [1])))
        {
          return false ;
        }
        if (ntk.is_on_critical_path (ntk.get_node (g1_fi [1])))
        {
          modify_associativity (fanin [0], g1_fi [0], g1_fi [1], n) ;
          return true ;
        }
        else
        {
          modify_associativity (fanin [0], g1_fi [1], g1_fi [0], n) ;
          return true ;
        }
      }
      else if (ntk.level (g0) > ntk.level (g1) + 1 && !ntk.is_complemented (fanin [0]))
      {
        if (ntk.is_on_critical_path (ntk.get_node (g0_fi [0])) && ntk.is_on_critical_path (ntk.get_node (g0_fi [1])))
        {
          return false ;
        }
        if (ntk.is_on_critical_path (ntk.get_node (g0_fi [1])))
        {
          modify_associativity (fanin [1], g0_fi [0], g0_fi [1], n) ;
          return true ;
        }
        else
        {
          modify_associativity (fanin [1], g0_fi [1], g0_fi [0], n) ;
          return true ;
        }
      }
    }
    else
      return false;
  }

  void modify_distributivity (signal a, signal b, signal c, node n)
  {
    signal g1 = ntk.create_and (!a, !c) ;
    signal g0 = ntk.create_and (b, !g1) ;
    ntk.substitute_node (n, !g0) ;
    //ntk.update_levels () ;
  }


  bool is_fi_comp (node n)
  {
    std::vector <signal> fanin ;
    ntk.foreach_fanin (n, [&](auto const& fi) {
      fanin.push_back (fi) ;
    }) ;
    return (ntk.is_complemented (fanin [0]) && ntk.is_complemented (fanin [1])) ;
  }



  /* Try the distributivity rule on node n. Return true if the network is updated. */
  bool try_distributivity( node n )
  {
    if  (!ntk.is_on_critical_path (n))
    {
      return false ;
    }
    if (is_fi_comp (n) && ntk.level (n) >= 2)
    {
      std::vector <signal> fanin ;
      ntk.foreach_fanin (n, [&](auto const& fi) {
        fanin.push_back (fi) ;
      }) ;
      node g1 = ntk.get_node (fanin [0]) ;
      node g2 = ntk.get_node (fanin [1]) ;

      if (!ntk.is_on_critical_path (g1) || !ntk.is_on_critical_path (g2))
      {
        return false ;
      }

      if (fanin.size () < 2)
      {
        return false ;
      }

      std::vector <signal> g1_fi ;
      ntk.foreach_fanin (g1, [&](auto const& fi) {
        g1_fi.push_back (fi) ;
      }) ;

      std::vector <signal> g2_fi ;
      ntk.foreach_fanin (g2, [&](auto const& fi) {
        g2_fi.push_back (fi) ;
      }) ;

      if (g1_fi.size () < 2)
      {
        return false ;
      }

      if (g2_fi.size () < 2)
      {
        return false ;
      }

      if ((ntk.get_node (g1_fi [0]) == ntk.get_node (g2_fi [0])) && (ntk.is_complemented (g1_fi [0]) == ntk.is_complemented (g2_fi [0])))
      {
        if (ntk.is_on_critical_path (ntk.get_node (g1_fi [1])) || ntk.is_on_critical_path (ntk.get_node (g2_fi [1])))
        {
          return false ;
        }
        modify_distributivity (g1_fi [1], g1_fi [0], g2_fi [1], n) ;
        return true ;
      }
      else if ((ntk.get_node (g1_fi [0]) == ntk.get_node (g2_fi [1])) && (ntk.is_complemented (g1_fi [0]) == ntk.is_complemented (g2_fi [1])))
      {
        if (ntk.is_on_critical_path (ntk.get_node (g1_fi [1])) || ntk.is_on_critical_path (ntk.get_node (g2_fi [0])))
        {
         return false ;
        }
        modify_distributivity (g1_fi [1], g1_fi [0], g2_fi [0], n) ;
        return true ;
      }
      else if ((ntk.get_node (g1_fi [1]) == ntk.get_node (g2_fi [0])) && (ntk.is_complemented (g1_fi [1]) == ntk.is_complemented (g2_fi [0])))
      {
        if (ntk.is_on_critical_path (ntk.get_node (g1_fi [0])) || ntk.is_on_critical_path (ntk.get_node (g2_fi [1])))
        {
          return false ;
        }
        modify_distributivity (g1_fi [0], g1_fi [1], g2_fi [1], n) ;
        return true ;
      }
      else if ((ntk.get_node (g1_fi [1]) == ntk.get_node (g2_fi [1])) && (ntk.is_complemented (g1_fi [1]) == ntk.is_complemented (g2_fi [1])))
      {
        if (ntk.is_on_critical_path (ntk.get_node (g1_fi [0])) || ntk.is_on_critical_path (ntk.get_node (g2_fi [0])))
        {
          return false ;
        }
        modify_distributivity (g1_fi [0], g1_fi [1], g2_fi [0], n) ;
        return true ;
      }
    }
    return false ;
  }

  /* Try the 3 layers distributivity rule on node n. Return true if the network is updated. */
  bool try_3_layer_distributivity( node n )
  {
    if (!ntk.is_on_critical_path (n))
    {
      return false ;
    }

    std::vector <signal> child ;
    ntk.foreach_fanin (n, [&](auto const& fi) {
      child.push_back (fi) ;
    }) ;
    if (ntk.level (ntk.get_node (child [1])) > ntk.level (ntk.get_node (child [0])))
    {
      std::swap (child [0], child [1]) ;
    }
    if (ntk.level (ntk.get_node (child [1])) + 2 >= ntk.level (ntk.get_node (child [0])))
    {
      return false ;
    }

    if (ntk.is_complemented (child [0]))
    {
      node g1 = ntk.get_node (child [0]) ;
      std::vector <signal> grandchild ;
      ntk.foreach_fanin (g1, [&](auto const& fi) {
        grandchild.push_back (fi) ;
      }) ;

      if (ntk.level (ntk.get_node (grandchild [1])) > ntk.level (ntk.get_node (grandchild [0])))
      {
        std::swap (grandchild [0], grandchild [1]) ;
      }

      if (ntk.is_on_critical_path (ntk.get_node (grandchild [0])) && ntk.is_on_critical_path (ntk.get_node (grandchild [1]))) //check that the critical is really critical
      {
        return false ; //do the same check also for children and children of the grandchildren
      }

      if (ntk.is_complemented (grandchild [0]))
      {
        node g2 = ntk.get_node (grandchild [0]) ;
        std::vector <signal> ggrandchild ;
        ntk.foreach_fanin (g2, [&](auto const& fi) {
          ggrandchild.push_back (fi) ;
        }) ;

        if (ntk.is_on_critical_path (ntk.get_node (ggrandchild [0])) && ntk.is_on_critical_path (ntk.get_node (ggrandchild [1])) )
        {
          return false ;
        }

        if (ntk.level (ntk.get_node (ggrandchild [1])) > ntk.level (ntk.get_node (ggrandchild [0])))
        {
          std::swap (ggrandchild [0], ggrandchild [1]) ;
        }
        signal gate3 = ntk.create_and (child [1], ggrandchild [1]) ;
        signal gate2 = ntk.create_and (ggrandchild [0], gate3) ;
        signal gate1 = ntk.create_and (!grandchild [1], child [1]);
        signal gate0 = ntk.create_and (!gate1, !gate2) ;
        ntk.substitute_node (n, !gate0) ;
        return true;
      }
    }
    return false ;
  }


private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */
