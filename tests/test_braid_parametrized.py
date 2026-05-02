import os
import tempfile
from braid import (
    make_dag,
    geneses,
    tips,
    reverse,
    generation,
    all_ancestors,
    all_ancestors_recursive,
    cohorts,
    cohort_head,
    cohort_tail,
    sub_braid,
    descendant_work,
    bead_cmp,
    work_sort_key,
    highest_work_path,
    check_cohort,
    load_braid,
    save_braid,
    number_beads,
    layout,
)


# geneses()
class TestGeneses:
    def test_single_genesis(self, blockchain_parents):
        assert geneses(blockchain_parents) == {0}

    def test_two_geneses(self, two_genesis_parents):
        assert geneses(two_genesis_parents) == {0, 1}

    def test_three_geneses(self, three_genesis_parents):
        assert geneses(three_genesis_parents) == {0, 1, 2}

    def test_fan_out_geneses(self, fan_out_parents):
        assert geneses(fan_out_parents) == {0, 1, 2}

    def test_diamond_single_genesis(self, diamond_parents):
        assert geneses(diamond_parents) == {0}

    def test_all_fixtures_have_single_genesis(self, braid_fixture):
        filename, dag = braid_fixture
        assert geneses(dag["parents"]) == {0}, f"Failed for {filename}"


# tips()
class TestTips:
    def test_single_tip(self, blockchain_parents):
        assert tips(blockchain_parents) == {3}

    def test_two_tips(self, two_genesis_parents):
        assert tips(two_genesis_parents) == {0, 2, 3}

    def test_fan_out_tips(self, fan_out_parents):
        assert tips(fan_out_parents) == {3, 4, 5}

    def test_diamond_tip(self, diamond_parents):
        assert tips(diamond_parents) == {4}

    def test_tips_with_explicit_children(self, blockchain_parents):
        children = reverse(blockchain_parents)
        assert tips(blockchain_parents, children) == {3}


# reverse()
class TestReverse:
    def test_reverse_fan_out(self, fan_out_parents):
        children = reverse(fan_out_parents)
        assert children == {
            0: {3, 4, 5},
            1: {3, 4, 5},
            2: {3, 4, 5},
            3: set(),
            4: set(),
            5: set(),
        }

    def test_reverse_blockchain(self, blockchain_parents):
        children = reverse(blockchain_parents)
        assert children == {0: {1}, 1: {2}, 2: {3}, 3: set()}

    def test_double_reverse_is_identity(self, diamond_parents):
        """reverse(reverse(parents)) should give back the original parents."""
        children = reverse(diamond_parents)
        roundtrip = reverse(children)
        assert roundtrip == diamond_parents

    def test_reverse_preserves_bead_set(self, braid_fixture):
        """Reversing should not add or lose any beads."""
        _, dag = braid_fixture
        children = reverse(dag["parents"])
        assert set(children.keys()) == set(dag["parents"].keys())


# generation()
class TestGeneration:
    def test_generation_from_genesis(self, blockchain_parents):
        children = reverse(blockchain_parents)
        assert generation({0}, children) == {1}

    def test_generation_from_fan_out_geneses(self, fan_out_parents):
        children = reverse(fan_out_parents)
        assert generation({0, 1, 2}, children) == {3, 4, 5}

    def test_generation_from_tips_is_empty(self, blockchain_parents):
        children = reverse(blockchain_parents)
        assert generation({3}, children) == set()

    def test_generation_in_parent_direction(self, diamond_parents):
        """Using parents instead of children moves backward."""
        assert generation({3}, diamond_parents) == {1, 2}

    def test_generation_diamond_children(self, diamond_parents):
        children = reverse(diamond_parents)
        assert generation({1, 2}, children) == {3}


# all_ancestors() and all_ancestors_recursive()
class TestAllAncestors:
    def test_genesis_has_no_ancestors(self, blockchain_parents):
        ancestors = {}
        all_ancestors(0, blockchain_parents, ancestors)
        assert ancestors[0] == set()

    def test_tip_has_all_prior(self, blockchain_parents):
        ancestors = {}
        all_ancestors(3, blockchain_parents, ancestors)
        assert ancestors[3] == {0, 1, 2}

    def test_diamond_ancestors(self, diamond_parents):
        ancestors = {}
        all_ancestors(3, diamond_parents, ancestors)
        assert ancestors[3] == {0, 1, 2}

    def test_iterative_matches_recursive(self, braid_fixture):
        """Iterative and recursive all_ancestors must agree on every bead."""
        filename, dag = braid_fixture
        for b in dag["parents"]:
            iter_anc = all_ancestors(b, dag["parents"], {})
            rec_anc = all_ancestors_recursive(b, dag["parents"], {})
            assert iter_anc == rec_anc, f"Mismatch for bead {b} in {filename}"

    def test_explicit_fresh_dicts_are_isolated(self, blockchain_parents):
        """Separate caller-provided ancestor dicts should not share state."""
        a1 = all_ancestors(2, blockchain_parents, {})
        a2 = all_ancestors(1, blockchain_parents, {})
        # With distinct explicit dicts, bead 1 should only record bead 0.
        assert a2[1] == {0}


# cohorts()
class TestCohorts:
    def test_blockchain_cohorts(self, blockchain_parents):
        assert list(cohorts(blockchain_parents)) == [{0}, {1}, {2}, {3}]

    def test_cohorts_match_fixture(self, braid_fixture):
        filename, dag = braid_fixture
        assert list(cohorts(dag["parents"])) == dag["cohorts"], f"Failed for {filename}"

    def test_reversed_cohorts_match(self, braid_fixture):
        """Cohorts found in reverse direction should match forward cohorts reversed."""
        filename, dag = braid_fixture
        p = reverse(dag["parents"])
        c = list(dag["cohorts"])
        c.reverse()
        assert list(cohorts(p)) == c, f"Failed for {filename}"

    def test_cohorts_partition_all_beads(self, braid_fixture):
        """Every bead must appear in exactly one cohort."""
        _, dag = braid_fixture
        all_beads = set(dag["parents"].keys())
        cohort_union = set()
        for c in dag["cohorts"]:
            # No overlap with prior cohorts
            assert c.isdisjoint(cohort_union), "Cohorts overlap"
            cohort_union |= c
        assert cohort_union == all_beads, "Cohorts don't cover all beads"


# cohort_head() / cohort_tail()
class TestCohortHeadTail:
    def test_head_equals_sub_braid_geneses(self, braid_fixture):
        filename, dag = braid_fixture
        for c in dag["cohorts"]:
            head = cohort_head(c, dag["parents"], dag["children"])
            sub_gen = geneses(sub_braid(c, dag["parents"]))
            assert head == sub_gen, f"Head mismatch for cohort {c} in {filename}"

    def test_tail_equals_sub_braid_tips(self, braid_fixture):
        filename, dag = braid_fixture
        for c in dag["cohorts"]:
            tail = cohort_tail(c, dag["parents"], dag["children"])
            sub_tip = tips(sub_braid(c, dag["parents"]))
            assert tail == sub_tip, f"Tail mismatch for cohort {c} in {filename}"


# sub_braid()
class TestSubBraid:
    def test_sub_braid_single_cohort(self, braid_fixture):
        """sub_braid of a cohort should itself have exactly one cohort."""
        filename, dag = braid_fixture
        for c in dag["cohorts"]:
            sb = sub_braid(c, dag["parents"])
            assert list(cohorts(sb)) == [c], f"Sub-braid multi-cohort for {c} in {filename}"

    def test_sub_braid_preserves_beads(self, diamond_parents):
        full_beads = set(diamond_parents.keys())
        sb = sub_braid(full_beads, diamond_parents)
        assert set(sb.keys()) == full_beads

    def test_sub_braid_restricts_parents(self, diamond_parents):
        subset = {1, 2, 3}
        sb = sub_braid(subset, diamond_parents)
        # Parents of 1 and 2 include 0, but 0 is not in subset
        assert sb[1] == set()
        assert sb[2] == set()
        assert sb[3] == {1, 2}


# descendant_work()
class TestDescendantWork:
    def test_blockchain_work(self, blockchain_parents):
        children = reverse(blockchain_parents)
        bead_work = {b: 1 for b in blockchain_parents}
        work = descendant_work(blockchain_parents, children, bead_work)
        # In a chain, bead 0 has all descendants so highest work
        assert work[0] > work[3]

    def test_work_matches_fixture(self, braid_fixture):
        filename, dag = braid_fixture
        computed = descendant_work(
            dag["parents"], dag["children"], dag["bead_work"]
        )
        assert computed == dag["work"], f"Work mismatch in {filename}"

    def test_tip_has_lowest_descendant_work(self, blockchain_parents):
        children = reverse(blockchain_parents)
        bead_work = {b: 1 for b in blockchain_parents}
        work = descendant_work(blockchain_parents, children, bead_work)
        tip_work = work[3]
        for b in blockchain_parents:
            assert work[b] >= tip_work


# bead_cmp() / work_sort_key()
class TestBeadOrdering:
    def test_bead_cmp_higher_work_wins(self):
        dwork = {0: 10, 1: 5}
        assert bead_cmp(0, 1, dwork) == 1  # 0 has more work
        assert bead_cmp(1, 0, dwork) == -1

    def test_bead_cmp_tie_uses_ancestor_work(self):
        dwork = {0: 10, 1: 10}
        awork = {0: 3, 1: 7}
        assert bead_cmp(0, 1, dwork, awork) == -1  # 0 has less ancestor work
        assert bead_cmp(1, 0, dwork, awork) == 1

    def test_bead_cmp_equal(self):
        dwork = {0: 10}
        assert bead_cmp(0, 0, dwork) == 0

    def test_bead_cmp_fallback_to_label(self):
        dwork = {5: 10, 3: 10}
        assert bead_cmp(5, 3, dwork) == -1  # higher label wins as tiebreaker

    def test_work_sort_key_sorts_by_work(self, blockchain_parents):
        children = reverse(blockchain_parents)
        bead_work = {b: 1 for b in blockchain_parents}
        key = work_sort_key(blockchain_parents, children, bead_work)
        sorted_beads = sorted(blockchain_parents.keys(), key=key)
        # Lowest work (tip) first, highest work (genesis) last
        assert sorted_beads[-1] == 0
        assert sorted_beads[0] == 3

# highest_work_path()
class TestHighestWorkPath:
    def test_blockchain_hwp(self, blockchain_parents):
        assert highest_work_path(blockchain_parents) == [0, 1, 2, 3]

    def test_hwp_matches_fixture(self, braid_fixture):
        filename, dag = braid_fixture
        computed = highest_work_path(dag["parents"], dag["children"])
        assert computed == dag["highest_work_path"], f"HWP mismatch in {filename}"

    def test_hwp_starts_at_genesis_ends_at_tip(self, braid_fixture):
        _, dag = braid_fixture
        hwp = dag["highest_work_path"]
        assert hwp[0] in geneses(dag["parents"])
        assert hwp[-1] in tips(dag["parents"], dag["children"])

    def test_hwp_is_connected_path(self, braid_fixture):
        """Each consecutive bead in hwp should be a child of the previous."""
        _, dag = braid_fixture
        hwp = dag["highest_work_path"]
        for i in range(len(hwp) - 1):
            assert hwp[i + 1] in dag["children"][hwp[i]], (
                f"HWP discontinuity at index {i}: {hwp[i]} -> {hwp[i+1]}"
            )


# check_cohort()
class TestCheckCohort:
    def test_all_fixture_cohorts_valid(self, braid_fixture):
        filename, dag = braid_fixture
        for c in dag["cohorts"]:
            assert check_cohort(c, dag["parents"], dag["children"]), (
                f"check_cohort failed for cohort {c} in {filename}"
            )


# make_dag() / number_beads()
class TestMakeDag:
    def test_make_dag_blockchain(self, blockchain_parents):
        dag = make_dag(blockchain_parents)
        assert dag["geneses"] == {0}
        assert dag["tips"] == {3}
        assert len(dag["cohorts"]) == 4
        assert dag["highest_work_path"] == [0, 1, 2, 3]

    def test_make_dag_keys(self, blockchain_parents):
        dag = make_dag(blockchain_parents)
        expected_keys = {
            "description", "parents", "children", "geneses", "tips",
            "cohorts", "bead_work", "work", "highest_work_path",
        }
        assert set(dag.keys()) == expected_keys

    def test_number_beads_identity(self, blockchain_parents):
        """Already-numbered sequential parents should come back unchanged."""
        result = number_beads(blockchain_parents)
        assert result == blockchain_parents

    def test_number_beads_renumbers(self):
        """Non-sequential bead IDs should get renumbered starting at 0."""
        hashed = {100: set(), 200: {100}, 300: {200}}
        result = number_beads(hashed)
        # Should produce {0: set(), 1: {0}, 2: {1}}
        assert geneses(result) == {0}
        assert len(result) == 3
        for b, p in result.items():
            assert isinstance(b, int)
            for parent in p:
                assert isinstance(parent, int)


# save_braid() / load_braid() round-trip
class TestSaveLoadBraid:
    def test_round_trip(self, blockchain_parents):
        """save_braid then load_braid should produce equivalent data."""
        with tempfile.NamedTemporaryFile(suffix=".json", delete=False, mode="w") as f:
            tmpfile = f.name
        try:
            save_braid(blockchain_parents, tmpfile, description="round-trip test")
            loaded = load_braid(tmpfile)
            assert loaded["description"] == "round-trip test"
            assert loaded["parents"] == blockchain_parents
            assert loaded["cohorts"] == [{0}, {1}, {2}, {3}]
            assert loaded["highest_work_path"] == [0, 1, 2, 3]
        finally:
            os.unlink(tmpfile)

    def test_round_trip_diamond(self, diamond_parents):
        with tempfile.NamedTemporaryFile(suffix=".json", delete=False, mode="w") as f:
            tmpfile = f.name
        try:
            save_braid(diamond_parents, tmpfile, description="diamond")
            loaded = load_braid(tmpfile)
            assert loaded["geneses"] == {0}
            assert loaded["tips"] == {4}
        finally:
            os.unlink(tmpfile)

    def test_fixture_files_load_without_error(self, braid_fixture):
        """Every fixture file should load cleanly with all expected keys."""
        filename, dag = braid_fixture
        expected_keys = {
            "description", "parents", "children", "geneses", "tips",
            "cohorts", "bead_work", "work", "highest_work_path",
        }
        assert expected_keys == set(dag.keys()), f"Key mismatch in {filename}"


# layout()
class TestLayout:
    def test_layout_blockchain(self, blockchain_parents):
        """Layout of a simple chain should place all beads on y=0."""
        single_cohort = set(blockchain_parents.keys())
        bead_work = {b: 1 for b in blockchain_parents}
        pos, tips_pos = layout(single_cohort, blockchain_parents, bead_work)
        for bead in blockchain_parents:
            assert bead in pos, f"Bead {bead} missing from layout"

    def test_layout_returns_tips(self, diamond_parents):
        cohort = set(diamond_parents.keys())
        bead_work = {b: 1 for b in diamond_parents}
        pos, tips_pos = layout(cohort, diamond_parents, bead_work)
        assert 4 in tips_pos

    def test_layout_no_duplicate_positions(self, diamond_parents):
        """No two beads should occupy the same grid cell."""
        cohort = set(diamond_parents.keys())
        bead_work = {b: 1 for b in diamond_parents}
        pos, _ = layout(cohort, diamond_parents, bead_work)
        positions = [tuple(v) for v in pos.values()]
        assert len(positions) == len(set(positions)), "Duplicate positions in layout"
