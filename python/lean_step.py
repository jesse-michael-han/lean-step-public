import os
import json
from tqdm import tqdm
from util import files_with_extension


def get_tactic_state(dp, sep="\t"):
    """
    Args:
      dp: LeanStepDatapoint in JSON format. The specification of this format is given by the
          `has_to_tactic_json` instance in `./src/data_util/lean_step.lean`

    Returns:
      A formatted tactic state.
    """
    hyps_strings_state = []
    last_tp = None
    for nm, tp in dp["hyps"]:
        if not last_tp == tp:
            hyps_strings_state.append(([nm], tp))
            last_tp = tp
        else:
            hyps_strings_state[-1][0].append(nm)

    hyps_strings = []
    n_hyps = len(hyps_strings_state)
    for i, (nms, tp) in enumerate(hyps_strings_state):
        hyps_strings.append(" ".join(nms) + " : " + tp + ("," if i < n_hyps - 1 else ""))

    goal = dp["goal"]
    goal_string = f"⊢ {goal}"
    return sep.join(hyps_strings + [goal_string])
    # hyps_strings_state = collections.defaultdict(list)
    # for nm, tp in dp["hyps"]:
    #     hyps_strings_state[tp].append(nm)
    # n_hyps = len(hyps_strings_state)
    # hyps_strings = []
    # for i, (tp, nms) in enumerate(hyps_strings_state.items()):
    #     hyps_strings.append(" ".join(nms) + " : " + tp + ("," if i < n_hyps-1 else ""))
    # goal = dp["goal"]
    # goal_string = f"⊢ {goal}"
    # return sep.join(hyps_strings + [goal_string])


def get_positive_hyps(dp):
    return [hyp for hyp, bit in zip(dp["hyps"], dp["hyps_mask"]) if bit]


def get_positive_premises(dp):
    return [premise for premise, bit in zip(dp["decl_premises"], dp["decl_premises_mask"])]


def get_proof_step_classification_datapoint(dp):
    ts = get_tactic_state(dp)
    positive_hyps = get_positive_hyps(dp)
    return (ts, positive_hyps)


def get_premise_selection_classification_datapoint(dp):
    ts = get_tactic_state(dp)
    premises = dp["decl_premises"]
    positive_premises = get_positive_premises(dp)
    return (ts, premises, positive_premises)


def get_theorem_name_prediction_datapoint(dp):
    return (dp["decl_tp"], dp["decl_nm"])


def get_next_lemma_prediction_datapoint(dp):
    return (get_tactic_state(dp), dp["next_lemma"])


def get_proof_term_prediction_datapoint(dp):
    return (get_tactic_state(dp), dp["proof_term"])


def get_skip_proof_datapoint(dp):
    return (dp["result"], dp["proof_term"])


def get_type_prediction_datapoint(dp):
    return (dp["result"], dp["goal"])


def get_ts_elab_datapoint(dp):
    return (get_tactic_state(dp), dp["verbose_goal"])


def get_proof_term_elab_datapoint(dp):
    return (dp["proof_term"], dp["verbose_proof_term"])


def get_result_elab_datapoint(dp):
    return (dp["result"], dp["verbose_result"])


def length_guard(result):
    LIMIT = 3800
    return all(len(v) < LIMIT for _, v in result.items())


class DatasetCreator:
    def __init__(self, fp):
        self.fp = fp

    def process_dp(dp):
        raise NotImplementedError


def to_type_annotation(xy):
    nm, tp = xy
    return "(" + nm + " : " + tp + ")"


class ProofStepClassificationDatasetCreator(DatasetCreator):
    """
    Creates proof step classification datapoints. The prompt is the goal state + "classify_locals".
    The completion is the sublist of the local assumptions in the goal state consisting of those
    assumptions which are actually used in the proof term which fulfills that goal state.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        ts, positive_hyps = get_proof_step_classification_datapoint(dp)
        positive_hyps = tuple(map(to_type_annotation, positive_hyps))
        result = {"goal": ts, "classify_locals": positive_hyps}
        result_msg = json.dumps(result)
        guard = lambda: len(positive_hyps) > 0  # noqa: E731
        if guard() and (not (ts, positive_hyps) in self.seen):
            self.seen.add((ts, positive_hyps))
            self.fp.write(result_msg + "\n")


class PremiseClassificationDatasetCreator(DatasetCreator):
    """
    Creates premise classification datapoints.
    The prompt is the goal state + "classify_premise" + the premise name and type, the completion
    is "true" or "false". This can be adapted to use the `classify_locals` idiom, but there are
     often many more premises than local assumptions.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        ts = get_tactic_state(dp)
        guard = lambda: any(dp["decl_premises_mask"])  # noqa: E731
        if guard():
            for (premise_nm, premise_tp), bit in zip(dp["decl_premises"], dp["decl_premises_mask"]):
                if not (ts, premise_nm, premise_tp) in self.seen:
                    self.seen.add((ts, premise_nm, premise_tp))
                    result = {
                        "goal": ts,
                        "classify_premise": (
                            "(" + premise_nm + " : " + premise_tp + ")" + f" {bit}"
                        ),
                    }
                    result_msg = json.dumps(result)
                    self.fp.write(result_msg + "\n")


class TheoremNamePredictionDatasetCreator(DatasetCreator):
    """
    Creates theorem name prediction datapoints.
    The prompt is the type of the theorem + "name". The completion is the name for the theorem
    that was registered in `mathlib`. Due to `mathlib` naming conventions, theorem names are
    essentially natural language summarizations of the type signature, so this is essentially
    a formal2informal translation/summarization task. Co-training on this should help when
    the model needs to guess unseen lemma names.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        tp, nm = get_theorem_name_prediction_datapoint(dp)
        if nm in self.seen:
            pass
        else:
            self.seen.add(nm)
            result = {"type": tp, "name": nm}
            result_msg = json.dumps(result)
            self.fp.write(result_msg + "\n")


class NextLemmaPredictionDatasetCreator(DatasetCreator):
    """
    Creates next lemma prediction datapoints.
    The prompt is the goal state + "next_lemma". The completion is the (name : type) of the next
    lemma which is applied, i.e. the head symbol of the proof term at point.
    This subsumes the proof-step task from MM GPT-f.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        ts, next_lemma = get_next_lemma_prediction_datapoint(dp)
        guard = lambda: next_lemma is not None and (not next_lemma[0] == "id")  # noqa: E731
        if guard():
            next_lemma = to_type_annotation(next_lemma)
            if not ((ts, next_lemma) in self.seen):
                self.seen.add((ts, next_lemma))
                result = {"goal": ts, "next_lemma": next_lemma}
                result_msg = json.dumps(result)
                self.fp.write(result_msg + "\n")


class ProofTermPredictionDatasetCreator(DatasetCreator):
    """
    Creates proof term prediction datapoints. The prompt is the goal state + "proof_term". The
    completion is the pretty-printed (non-negligible chance this will fail to re-parse!)
    proof term at point.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        ts, proof_term = get_proof_term_prediction_datapoint(dp)
        if True:
            if not ((ts, proof_term) in self.seen):
                self.seen.add((ts, proof_term))
                result = {"goal": ts, "proof_term": proof_term}
                result_msg = json.dumps(result)
                self.fp.write(result_msg + "\n")


class SkipProofDatasetCreator(DatasetCreator):
    """
    Creates skip-proof prediction datapoints. The prompt is the pretty-printed "partial result"
    at point, i.e. the entire proof term of the declaration with the proof term at point
    replaced by a "PREDICT" token, plus "proof_term". The completion is the proof term at point.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        result, proof_term = get_skip_proof_datapoint(dp)
        guard = lambda: "PREDICT" in result  # noqa: E731
        if guard():
            if not ((result, proof_term) in self.seen):
                self.seen.add((result, proof_term))
                result = {"skip_proof": result, "proof_term": proof_term}
                result_msg = json.dumps(result)
                self.fp.write(result_msg + "\n")


class TypePredictionDatasetCreator(DatasetCreator):
    """
    Creates type prediction datapoints. The prompt is the pretty-printed "partial result" at point,
    plus "goal". The completion is the _type_ of the proof term at point, which is not explicit
    in the pretty-printed partial result.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        result, goal = get_type_prediction_datapoint(dp)
        guard = lambda: "PREDICT" in result  # noqa: E731
        if guard():
            if not ((result, goal) in self.seen):
                self.seen.add((result, goal))
                result = {"skip_proof": result, "goal": goal}
                result_msg = json.dumps(result)
                self.fp.write(result_msg + "\n")


class TSElabDatasetCreator(DatasetCreator):
    """
    Creates tactic state elaboration datapoints. The prompt is the pretty-printed
    goal state + "elab_goal". The completion is the verbosely-printed goal state
    (i.e. type annotations, explicit arguments, etc.)
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        goal, goal_elab = get_ts_elab_datapoint(dp)
        guard = lambda: len(goal) < len(goal_elab)  # noqa: E731
        if guard():
            if not ((goal, goal_elab) in self.seen):
                self.seen.add((goal, goal_elab))
                result = {"goal": goal, "elab_goal": goal_elab}
                result_msg = json.dumps(result)
                self.fp.write(result_msg + "\n")


class ProofTermElabDatasetCreator(DatasetCreator):
    """
    Creates proof term elaboration datapoints. The prompt is the pretty-printed proof
    term at point, plus "elab_proof_term". The completion is the verbosely-printed
    proof term at point (i.e. type annotations, explicit arguments, etc.)
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        proof_term, proof_term_elab = get_proof_term_elab_datapoint(dp)
        guard = lambda: len(proof_term) < len(proof_term_elab)  # noqa: E731
        if guard():
            if not ((proof_term, proof_term_elab) in self.seen):
                self.seen.add((proof_term, proof_term_elab))
                result = {"proof_term": proof_term, "elab_proof_term": proof_term_elab}
                result_msg = json.dumps(result)
                self.fp.write(result_msg + "\n")


class ResultElabDatasetCreator(DatasetCreator):
    """
    Creates result elaboration datapoints. The prompt is the pretty-printed partial
    result plus "result_elab". The completion is the verbosely-printed partial result.
    """

    def __init__(self, fp):
        super().__init__(fp)
        self.seen = set()

    def process_dp(self, dp):
        result, result_elab = get_result_elab_datapoint(dp)
        guard = lambda: len(result) < len(result_elab)  # noqa: E731
        if guard():
            if not ((result, result_elab) in self.seen):
                self.seen.add((result, result_elab))
                result = {"result": result, "result_elab": result_elab}
                result_msg = json.dumps(result)
                self.fp.write(result_msg + "\n")


def create_datasets(data_dir: str, dest_dir: str):
    try:
        assert os.path.exists(data_dir)
    except AssertionError:
        raise Exception(f"[create_datasets] ERROR: DATA_DIR {data_dir} MUST EXIST")

    if not os.path.exists(dest_dir):
        os.makedirs(dest_dir)

    dataset_creators = [
        ProofStepClassificationDatasetCreator(
            open(os.path.join(dest_dir, "proof_step_classification.json"), "w")
        ),
        PremiseClassificationDatasetCreator(
            open(os.path.join(dest_dir, "premise_classification.json"), "w")
        ),
        TheoremNamePredictionDatasetCreator(
            open(os.path.join(dest_dir, "theorem_name_prediction.json"), "w")
        ),
        NextLemmaPredictionDatasetCreator(
            open(os.path.join(dest_dir, "next_lemma_prediction.json"), "w")
        ),
        ProofTermPredictionDatasetCreator(
            open(os.path.join(dest_dir, "proof_term_prediction.json"), "w")
        ),
        SkipProofDatasetCreator(open(os.path.join(dest_dir, "skip_proof.json"), "w")),
        TypePredictionDatasetCreator(open(os.path.join(dest_dir, "type_prediction.json"), "w")),
        TSElabDatasetCreator(open(os.path.join(dest_dir, "ts_elab.json"), "w")),
        ProofTermElabDatasetCreator(open(os.path.join(dest_dir, "proof_term_elab.json"), "w")),
        ResultElabDatasetCreator(open(os.path.join(dest_dir, "result_elab.json"), "w")),
    ]

    if not os.path.exists(dest_dir):
        os.makedirs(dest_dir)

    json_files = files_with_extension(data_dir, "json")
    print("JSON FILES: ", json_files)
    for json_file in tqdm(json_files):
        line = 0
        try:
            with open(json_file, "r") as json_file_handle:
                for json_line in json_file_handle:
                    line += 1
                    try:
                        dp = json.loads(json_line)
                        for dc in dataset_creators:
                            dc.process_dp(dp)
                    except Exception as e:
                        print(f"BAD LINE IN FILE: {json_file} EXCEPTION: {e}")
        except Exception as e:
            print(f"BAD FILE: {json_file} LINE: {line}: EXCEPTION: {e}")


def create_lm_sequence(dp_json):
    """
  Input: a JSON loaded from one of the `lean_step` JSONlines-formatted datasets
  Output: A string for language modelling.
  """
    (prompt_keyword, prompt_text), (completion_keyword, completion_text) = list(dp_json.items())
    prompt = prompt_keyword.upper() + " " + str(prompt_text)
    completion = completion_keyword.upper() + " " + str(completion_text)
    return prompt + " " + completion


def _parse_main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument(
        "data_dir", help="directory containing shard_{k}.json files created by parallel_data_gen"
    )
    parser.add_argument(
        "dest_dir",
        help="destination directory JSONlines-formatted dataset files extracted from data_dir",
    )
    return parser.parse_args()


if __name__ == "__main__":
    opts = _parse_main()
    create_datasets(**vars(opts))
