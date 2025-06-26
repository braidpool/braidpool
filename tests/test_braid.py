import unittest
from braid import *

class TestCohortMethods(unittest.TestCase):
    """ Test harness for unittest. """
    parents1 = {0:set(), 1:{0}, 2:{1}, 3:{2}} # blockchain
    parents2 = {0:set(), 1:set(), 2:{1}, 3:{1}}
    parents3 = {0:set(), 1:set(), 2:set(), 3:{1}, 4:{0}}
    parents4 = {0:set(), 1:set(), 2:set(), 3:{0,1,2}, 4:{0,1,2}, 5:{0,1,2}}
    diamond  = {0:set(), 1:{0}, 2:{0}, 3:{1,2}, 4:{3}}

    def test_geneses1(self):
        self.assertEqual(geneses(self.parents1), {0})

    def test_geneses2(self):
        self.assertEqual(geneses(self.parents2), {0, 1})

    def test_geneses3(self):
        self.assertEqual(geneses(self.parents3), {0, 1, 2})

    def test_geneses_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            self.assertEqual(geneses(dag["parents"]), {0})

    def test_tips1(self):
        parents1 = {0:set(), 1:[0], 2:[1], 3:[2]}
        self.assertEqual(tips(parents1), {3})

    def test_tips2(self):
        parents2 = {0:set(), 1:[0], 2:[1], 3:[1]}
        self.assertEqual(tips(parents2), {2,3})

    def test_tips3(self):
        parents3 = {0:set(), 1:set(), 2:set(), 3:[0,1,2], 4:[0,1,2], 5:[0,1,2]}
        self.assertEqual(tips(parents3), {3,4,5})

    def test_reverse(self):
        self.assertEqual(reverse(self.parents4),
                         {0: {3, 4, 5}, 1: {3, 4, 5}, 2: {3, 4, 5}, 3: set(), 4: set(), 5: set()})

    def test_cohorts(self):
        """ Test cohorts for a trivial blockchain-like braid. """
        self.assertEqual(list(cohorts(self.parents1)), [{0}, {1}, {2}, {3}])

    def test_cohorts_files(self):
        """ Test an assortment of example *.json files. """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            self.assertEqual(list(cohorts(dag["parents"])), dag["cohorts"])

    def test_cohorts_reversed_files(self):
        """ Does it find the same cohorts in the forward and backward directions? """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            p = reverse(dag["parents"])
            c = dag["cohorts"]
            c.reverse()
            self.assertEqual(list(cohorts(p)), c, msg="Test file: {filename}")

    def test_highest_work_path_blockchain(self):
        self.assertEqual(highest_work_path(self.parents1, reverse(self.parents1)), [0,1,2,3])

    def test_highest_work_path_diamond(self):
        self.assertEqual(highest_work_path(self.diamond, reverse(self.diamond)), [0,1,3,4])

    def test_higest_work_path_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            msg = f"Test file: {filename}"
            dag = load_braid(TEST_CASE_DIR+filename)
            self.assertEqual(highest_work_path(dag["parents"], dag["children"]), dag["highest_work_path"], msg=msg)

    def test_check_cohort_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            msg = f"Test file: {filename}"
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                self.assertEqual(check_cohort(c, dag["parents"], dag["children"]), True, msg=msg)

    def test_check_work_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            msg = f"Test file: {filename}"
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                self.assertEqual(dag["work"], descendant_work(dag["parents"], dag["children"], dag["bead_work"]),
                                    msg=msg)

    def test_sub_braid_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                msg = f"Test file: {filename}"
                self.assertEqual(geneses(sub_braid(c, dag["parents"])),
                                 cohort_head(c, dag["parents"], dag["children"]), msg=msg)
                self.assertEqual(tips(sub_braid(c, dag["parents"])),
                                 cohort_tail(c, dag["parents"], dag["children"]), msg=msg)
                self.assertEqual(list(cohorts(sub_braid(c, dag["parents"]))),
                                 [c], msg=msg)

    def test_head_tail_files(self):
        """ Test that cohort_head and cohort_tail do the same thing as geneses and tips. """
        for filename in sorted([filename for filename in
                                os.listdir(TEST_CASE_DIR) if
                                filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                msg = f"Test file: {filename}"
                self.assertEqual(cohort_head(c, dag["parents"], dag["children"]),
                                 geneses(sub_braid(c, dag["parents"])), msg=msg)
                self.assertEqual(cohort_tail(c, dag["parents"], dag["children"]),
                                 tips(sub_braid(c, dag["parents"])), msg=msg)

    def test_all_ancestors(self):
        """ Test that the iterative and recursive definitions of all_ancestors match.
        """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            for b in dag["parents"]:
                msg = f"Test file: {filename}"
                self.assertEqual(all_ancestors(b, dag["parents"]), all_ancestors_recursive(b, dag["parents"]), msg=msg)
    def test_layout(self):
        """ Create cohort layout json files for validating layout function. """
        if not os.path.exists("layouts"):
            os.makedirs("layouts")
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            previous_cohort_tips = None
            for (c, i) in zip(dag["cohorts"], range(len(dag["cohorts"]))):
                with open("layouts/" + filename.split('.')[0] + f"_{i}_layout.json", 'w', encoding="utf8") as file:
                    L, previous_cohort_tips = layout(c, dag["parents"], dag["bead_work"], previous_cohort_tips)
                    file.write(json.dumps([L, previous_cohort_tips], indent=4))

if __name__ == "__main__":
    unittest.main()
