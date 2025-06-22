use crate::engine::variables::IntegerVariable;
use crate::propagators::CumulativeParameters;
use crate::propagators::CumulativePropagatorOptions;
use crate::propagators::ArgTask;
use crate::propagators::Task;
use crate::propagators::util::create_tasks;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::ReadDomains;
use crate::engine::propagation::PropagationContextMut;
use crate::propagators::util::register_tasks;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::statistics::StatisticLogger;

use crate::predicate;
use crate::predicates::Predicate;
use crate::predicates::PropositionalConjunction;

use std::rc::Rc;

use crate::basic_types::PropagationStatusCP;


use std::cmp::{max, min};
use std::fmt;

const EPSILON: f64 = 1e-9;

static mut NO_ENERGY: i32 = 0;
static mut NO_REMOVAL: i32 = 0;
static mut NO_CHANGE: i32 = 0;

static mut TOTAL_ENERGY: i32 = 0;
static mut TOTAL_EXPLANATIONS: i32 = 0;
static mut NORMALIZED_ENERGY: f64 = 0.0;

#[derive(Clone, Debug)]
pub(crate) struct EnergeticReasoning<Var> {
    /// Stores the input parameters to the cumulative constraint
    parameters: CumulativeParameters<Var>,
}

struct Statistics {
    no_energy: i32,
    no_removal: i32,
    no_change: i32,
    total_energy: i32,
    total_explanations: i32,
    normalized_energy: f64
}

impl fmt::Display for Statistics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "NoEnergyIntervals, NoRemovedTasksIntervals, NoChangeIntervals, TotalEnergyToBeRemoved, TotalExplanations, TotalNormalizedEnergy - {}, {}, {}, {}, {}, {}",
            self.no_energy, self.no_removal, self.no_change, self.total_energy, self.total_explanations, self.normalized_energy
        )
    }
}

impl<Var: IntegerVariable + 'static> EnergeticReasoning<Var> {
    pub(crate) fn new(
        arg_tasks: &[ArgTask<Var>],
        capacity: i32,
        cumulative_options: CumulativePropagatorOptions,
    ) -> EnergeticReasoning<Var> {
        let tasks = create_tasks(arg_tasks);
        let parameters = CumulativeParameters::new(tasks, capacity, cumulative_options);

        EnergeticReasoning {
            parameters
        }
    }
}
fn add_interval(
    interval_vec: &mut Vec<(i32, i32)>,
    interval: (i32, i32),
){
    if interval.0 < interval.1 {
        interval_vec.push(interval);
    }
}

fn generate_all_intervals<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context,
    parameters: &CumulativeParameters<Var>
) -> Vec<(i32, i32)> {
    let mut intervals: Vec<(i32, i32)> = Vec::new();
    for task1 in parameters.tasks.iter() {
        for task2 in parameters.tasks.iter() {
            let est_i = context.lower_bound(&task1.start_variable);
            let lst_i = context.upper_bound(&task1.start_variable);
            let ect_i = est_i + task1.processing_time;
            let lct_i = lst_i + task1.processing_time;

            let est_j = context.lower_bound(&task2.start_variable);
            let lst_j = context.upper_bound(&task2.start_variable);
            let ect_j = est_j + task2.processing_time;
            let lct_j = lst_j + task2.processing_time;

            if est_i <= est_j && lct_j >= lct_i {
                add_interval(&mut intervals, (est_i, lct_j));
            }

            if est_i > est_j && est_i < ect_j && est_i < lst_j && est_j + lct_j - est_i >= lct_i {
                add_interval(&mut intervals, (est_i, est_j + lct_j - est_i));
            }

            if est_i > est_j && est_i < ect_j && est_i >= lst_j && ect_j >= lct_i {
                add_interval(&mut intervals, (est_i, ect_j));
            }

            if lst_i <= est_j && lct_j < lct_i && lct_j > lst_i && lct_j <= ect_j {
                add_interval(&mut intervals, (lst_i, lct_j));
            }

            if lst_i > est_j && lst_i < ect_j && lst_i < lst_j && lst_i < est_j + lct_j - lst_i && est_j + lct_j - lst_i <= ect_i && est_j + lct_j - lst_i < lct_i {
                add_interval(&mut intervals, (lst_i, est_j + lct_j - lst_i));
            }

            if lst_i > est_j && lst_i < ect_j && lst_i >= lst_j && ect_j < lct_i && ect_j > lst_i && ect_j <= ect_i{
                add_interval(&mut intervals, (lst_i, ect_j));
            }

            if lct_j < lct_i && lct_j > lst_i && lct_j > ect_i && est_i + lct_i - lct_j <= lst_j {
                add_interval(&mut intervals, (est_i + lct_i - lct_j, lct_j));
            }

            if ect_j < lct_i && ect_j > lst_i && ect_j > ect_i && lst_j <= est_i + lct_i - ect_j && est_i + lct_i - ect_j < ect_j && est_j < est_i + lct_i - ect_j {
                add_interval(&mut intervals, (est_i + lct_i - ect_j, ect_j));
            }
        }
    }
    intervals
}

fn generate_left_intervals<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context,
    skip_task: &Rc<Task<Var>>,
    parameters: &CumulativeParameters<Var>
) -> Vec<(i32, i32)> {
    let est_a = context.lower_bound(&skip_task.start_variable);
    let lst_a = context.upper_bound(&skip_task.start_variable);
    let ect_a = est_a + skip_task.processing_time;
    let lct_a = lst_a + skip_task.processing_time;

    let mut intervals: Vec<(i32, i32)> = Vec::new();
    for task in parameters.tasks.iter() {
        let est_i = context.lower_bound(&task.start_variable);
        let lst_i = context.upper_bound(&task.start_variable);
        let ect_i = est_i + task.processing_time;
        let lct_i = lst_i + task.processing_time;

        if std::ptr::eq(task, skip_task){
            continue;
        }

        if est_i < lst_a && lct_i < ect_a {
            add_interval(&mut intervals, (est_i, ect_a));
        }

        if est_i + lct_i - ect_a < ect_a && est_i + lct_i - ect_a < lst_a && ect_a < lct_i && ect_a > lst_i && ect_a > ect_i {
            add_interval(&mut intervals, (est_i + lct_i - ect_a, ect_a));
        }

        if lst_i < lst_a && ect_a < lct_i && ect_a > lst_i && ect_a <= ect_i {
            add_interval(&mut intervals, (lst_i, ect_a));
        }


        if est_a <= est_i && lct_i < lct_a {
            add_interval(&mut intervals, (est_a, lct_i));
        }

        if est_a > est_i && est_a < ect_i && est_a < lst_i && est_i + lct_i - est_a > est_a && est_i + lct_i - est_a < lct_a {
            add_interval(&mut intervals, (est_a, est_i + lct_i - est_a));
        }

        if est_a > est_i && est_a < ect_i && est_a >= lst_i && lct_i < lct_a {
            add_interval(&mut intervals, (est_a, ect_i));
        }

    }
    add_interval(&mut intervals, (est_a, ect_a));
    intervals
}

fn generate_right_intervals<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context,
    skip_task: &Rc<Task<Var>>,
    parameters: &CumulativeParameters<Var>
) -> Vec<(i32, i32)> {
    let est_a = -context.upper_bound(&skip_task.start_variable) - &skip_task.processing_time;
    let lst_a = -context.lower_bound(&skip_task.start_variable) - &skip_task.processing_time;
    let ect_a = est_a + skip_task.processing_time;
    let lct_a = lst_a + skip_task.processing_time;

    let mut intervals: Vec<(i32, i32)> = Vec::new();
    for task in parameters.tasks.iter() {
        if std::ptr::eq(task, skip_task) {
            continue;
        }

        let est_i = -context.upper_bound(&task.start_variable) - &skip_task.processing_time;
        let lst_i = -context.lower_bound(&task.start_variable) - &skip_task.processing_time;
        let ect_i = est_i + task.processing_time;
        let lct_i = lst_i + task.processing_time;

        if est_i < lst_a && lct_i < ect_a {
            add_interval(&mut intervals, (-ect_a - &skip_task.processing_time, -est_i - &skip_task.processing_time));
        }

        if est_i + lct_i - ect_a < ect_a && est_i + lct_i - ect_a < lst_a &&
            ect_a < lct_i && ect_a > lst_i && ect_a > ect_i {
            add_interval(&mut intervals, (-ect_a - &skip_task.processing_time, -(est_i + lct_i - ect_a) - &skip_task.processing_time));
        }

        if lst_i < lst_a && ect_a < lct_i && ect_a > lst_i && ect_a <= ect_i {
            add_interval(&mut intervals, (-ect_a - &skip_task.processing_time, -lst_i - &skip_task.processing_time));
        }


        if est_a <= est_i && lct_i < lct_a {
            add_interval(&mut intervals, (-lct_i - &skip_task.processing_time, -est_a - &skip_task.processing_time));
        }

        if est_a > est_i && est_a < ect_i && est_a < lst_i && est_i + lct_i - est_a > est_a && est_i + lct_i - est_a < lct_a {
            add_interval(&mut intervals, (-(est_i + lct_i - est_a) - &skip_task.processing_time, -est_a - &skip_task.processing_time));
        }

        if est_a > est_i && est_a < ect_i && est_a >= lst_i && lct_i < lct_a {
            add_interval(&mut intervals, (-ect_i - &skip_task.processing_time, -est_a - &skip_task.processing_time));
        }
    }

    add_interval(&mut intervals, (-ect_a - &skip_task.processing_time, -est_a - &skip_task.processing_time));

    intervals
}


fn left_shift<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context,
    interval: (i32, i32),
    task: &Task<Var>
) -> i32 {
    let est = context.lower_bound(&task.start_variable);
    let ect = est + task.processing_time;
    max(0, min(ect, interval.1) - max(est, interval.0))
}

fn right_shift<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context,
    interval: (i32, i32),
    task: &Task<Var>
) -> i32 {
    let lst = context.upper_bound(&task.start_variable);
    let lct = lst + task.processing_time;
    max(0, min(lct, interval.1) - max(lst, interval.0))
}

fn minimum_interval<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context,
    interval: (i32, i32),
    task: &Task<Var>
) -> i32 {
    min(left_shift(context, interval, task), right_shift(context, interval, task))
}

struct TaskBounds<'a, Var: IntegerVariable + 'static>{
    lb: i32,
    ub: i32,
    lb_init: i32,
    ub_init: i32,
    ls: i32,
    rs: i32,
    task: &'a Task<Var>
}

impl<'a, Var: IntegerVariable + 'static> TaskBounds<'a, Var> {
    fn expand_domain(&mut self, interval: (i32, i32)) {
        let mi = min(self.ls, self.rs);
        self.lb = interval.0 - self.task.processing_time + mi;
        self.ub = interval.1 - mi;
        self.ls = mi;
        self.rs = mi;
    }
    fn shift_out(&mut self, overload: &mut i32) -> bool{
        if self.ls <= 0 || self.rs <= 0 || *overload <= self.task.resource_usage{
            return false;
        }
        self.ls -= 1;
        self.rs -= 1;
        self.lb -= 1;
        self.ub += 1;
        *overload -= self.task.resource_usage;
        return true;
    }
    fn energy(&self) -> i32{
        min(self.ls, self.rs) * self.task.resource_usage
    }
    fn probability(&self) -> f64{
        let lb = max(self.lb, self.lb_init);
        let ub = min(self.ub, self.ub_init);
        - ((ub as f64 - lb as f64 ) / (self.ub_init as f64 - self.lb_init as f64)).ln()
    }
}

fn expand_domains<Var: IntegerVariable + 'static>(
    task_bounds: &mut Vec<TaskBounds<Var>>,
    interval: (i32, i32),
){
    for task_bound in task_bounds.iter_mut(){
        task_bound.expand_domain(interval);
    }
}

fn shift_tasks<Var: IntegerVariable + 'static>(
    task_bounds: &mut Vec<TaskBounds<Var>>,
    overload: &mut i32,
) {
    task_bounds.sort_by_key(|tb| tb.task.resource_usage);
    for task_bound in task_bounds.iter_mut(){
        while task_bound.shift_out(overload) {}
    }
    task_bounds.retain(|tb| tb.rs > 0 && tb.ls > 0);
}

fn remove_tasks_greedy<Var: IntegerVariable + 'static>(
    task_bounds: &mut Vec<TaskBounds<Var>>,
    overload: &mut i32,
){
    task_bounds.sort_by_key(|tb| tb.energy());

    task_bounds.retain(|task_bound| {
        if task_bound.energy() < *overload {
            *overload -= task_bound.energy();
            false
        } else {
            true
        }
    });
}

fn remove_tasks_knapsack<Var: IntegerVariable + 'static>(
    task_bounds: &mut Vec<TaskBounds<Var>>,
    overload: &mut i32,
){
    if *overload <= 1 {
        return;
    }
    let n = task_bounds.len();
    let w = *overload - 1;
    let mut dp: Vec<Vec<f64>> = vec![vec![0.0; w as usize + 1]; n + 1];

    for i in 0..=n {
        for j in 0..=w as usize {
            if i == 0 || j == 0 {
                continue;
            }
            let mut pick_value = 0.0;
            if task_bounds[i - 1].energy() <= j as i32 {
                pick_value = task_bounds[i - 1].probability() + dp[i - 1][j - task_bounds[i - 1].energy() as usize];
            }
            dp[i][j] = f64::max(pick_value, dp[i - 1][j]);
        }
    }

    let mut res = dp[n][w as usize];
    let mut w_temp = w;
    let mut i = n;

    while i > 0 && res > 0.0 {
        if (res - dp[i - 1][w_temp as usize]).abs() > EPSILON {
            res = res - task_bounds[i - 1].probability();
            w_temp = w_temp - task_bounds[i - 1].energy();
            *overload -= task_bounds[i - 1].energy();
            task_bounds.remove(i - 1);
        }
        i -= 1;
    }
}

fn create_conflict_explanation_base<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context, 
    interval: (i32, i32),
    overload: i32,
    parameters: &CumulativeParameters<Var>) -> Vec<Predicate>
{
    let mut task_bounds: Vec<TaskBounds<Var>> = Vec::new();
    for task in parameters.tasks.iter() {
        let ls: i32 = left_shift(context, interval, task);
        let rs: i32 = right_shift(context, interval, task);
        if ls > 0 && rs > 0 {
            task_bounds.push(TaskBounds{
                lb: context.lower_bound(&task.start_variable),
                ub: context.upper_bound(&task.start_variable),
                lb_init: context.lower_bound_after_root_propagation(&task.start_variable),
                ub_init: context.upper_bound_after_root_propagation(&task.start_variable),
                ls,
                rs,
                task
            });
        }
    }

    if overload <= 1 {
        unsafe { NO_ENERGY += 1 };
    }
    unsafe { TOTAL_ENERGY += overload - 1 };
    unsafe { TOTAL_EXPLANATIONS += 1 };
    if let Some(min_usage) = task_bounds
    .iter()
    .map(|tb| tb.task.resource_usage)
    .min()
    {
        unsafe { NORMALIZED_ENERGY += (overload - 1) as f64 / min_usage as f64 };
    }

    expand_domains(&mut task_bounds, interval);
    let mut maximum_overload = overload;
    let overload_before = overload;
    //remove_tasks_greedy(&mut task_bounds, &mut maximum_overload);
    remove_tasks_knapsack(&mut task_bounds, &mut maximum_overload);
    if overload_before == maximum_overload {
        unsafe { NO_REMOVAL += 1 };
    }
    shift_tasks(&mut task_bounds, &mut maximum_overload);
    if overload_before == maximum_overload {
        unsafe { NO_CHANGE += 1 };
    }
    let mut predicates: Vec<Predicate> = Vec::new();
    for task_bound in task_bounds.iter_mut(){
        predicates.push(predicate!(task_bound.task.start_variable >= task_bound.lb));
        predicates.push(predicate!(task_bound.task.start_variable <= task_bound.ub));
    }
    predicates
}

fn create_propagation_explanation_base<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context, 
    interval: (i32, i32),
    skip_task: &Rc<Task<Var>>,
    overload: i32,
    parameters: &CumulativeParameters<Var>) -> Vec<Predicate>
{
    let mut task_bounds: Vec<TaskBounds<Var>> = Vec::new();
    for task in parameters.tasks.iter() {
        if std::ptr::eq(skip_task, task) {
            continue;
        }
        let ls: i32 = left_shift(context, interval, task);
        let rs: i32 = right_shift(context, interval, task);
        if ls > 0 && rs > 0 {
            task_bounds.push(TaskBounds{
                lb: context.lower_bound(&task.start_variable),
                ub: context.upper_bound(&task.start_variable),
                lb_init: context.lower_bound_after_root_propagation(&task.start_variable),
                ub_init: context.upper_bound_after_root_propagation(&task.start_variable),
                ls,
                rs,
                task
            });
        }
    }
    if overload <= 1 {
        unsafe { NO_ENERGY += 1 };
    }
    unsafe { TOTAL_ENERGY += overload - 1 };
    unsafe { TOTAL_EXPLANATIONS += 1 };
    if let Some(min_usage) = task_bounds
    .iter()
    .map(|tb| tb.task.resource_usage)
    .min()
    {
        unsafe { NORMALIZED_ENERGY += (overload - 1) as f64 / min_usage as f64 };
    }

    expand_domains(&mut task_bounds, interval);
    let mut maximum_overload = overload;
    let overload_before = overload;
    //remove_tasks_greedy(&mut task_bounds, &mut maximum_overload);
    remove_tasks_knapsack(&mut task_bounds, &mut maximum_overload);
    if overload_before == maximum_overload {
        unsafe { NO_REMOVAL += 1 };
    }
    shift_tasks(&mut task_bounds, &mut maximum_overload);
    if overload_before == maximum_overload {
        unsafe { NO_CHANGE += 1 };
    }
    let mut predicates: Vec<Predicate> = Vec::new();
    for task_bound in task_bounds.iter_mut(){
        predicates.push(predicate!(task_bound.task.start_variable >= task_bound.lb));
        predicates.push(predicate!(task_bound.task.start_variable <= task_bound.ub));
    }
    predicates
}

fn create_conflict_explanation<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context, 
    interval: (i32, i32),
    overload: i32,
    parameters: &CumulativeParameters<Var>) -> PropositionalConjunction
{
    PropositionalConjunction::new(create_conflict_explanation_base(context, interval, overload, parameters))
}

fn create_propagation_explanation_left<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context, 
    interval: (i32, i32),
    task: &Rc<Task<Var>>,
    overload: i32,
    parameters: &CumulativeParameters<Var>) -> PropositionalConjunction
{
    let mut predicates: Vec<Predicate> = create_propagation_explanation_base(context, interval, task, overload, parameters);
    predicates.push(predicate!(task.start_variable >= context.lower_bound(&task.start_variable)));
    PropositionalConjunction::new(predicates)
}

fn create_propagation_explanation_right<Context: ReadDomains + Copy, Var: IntegerVariable + 'static>(
    context: Context, 
    interval: (i32, i32),
    task: &Rc<Task<Var>>,
    overload: i32,
    parameters: &CumulativeParameters<Var>) -> PropositionalConjunction
{
    let mut predicates: Vec<Predicate> = create_propagation_explanation_base(context, interval, task, overload, parameters);
    predicates.push(predicate!(task.start_variable <= context.upper_bound(&task.start_variable)));
    PropositionalConjunction::new(predicates)
}

impl<Var: IntegerVariable + 'static> Propagator for EnergeticReasoning<Var> {

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        let intervals: Vec<(i32, i32)> = generate_all_intervals(context.as_readonly(), &self.parameters);

        for (start, end) in &intervals {
            let maximum_energy: i32 = self.parameters.capacity * (end - start);
            let mut used_energy: i32 = 0;
            for task in self.parameters.tasks.iter() {
                used_energy += minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
            }
            if used_energy > maximum_energy{
                let overload = used_energy - maximum_energy;
                return Err(create_conflict_explanation(context.as_readonly(), (*start, *end), overload, &self.parameters).into());
            }
            for task in self.parameters.tasks.iter() {
                used_energy -= minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                let available_energy = maximum_energy - used_energy;
                let updated_lower_bound = end - available_energy / task.resource_usage;
                let updated_upper_bound = start + (available_energy + task.resource_usage - 1) / task.resource_usage - task.processing_time;
                let ls = left_shift(context.as_readonly(), (*start, *end), task);
                let rs = right_shift(context.as_readonly(), (*start, *end), task);
                if available_energy < ls * task.resource_usage
                && context.lower_bound(&task.start_variable) < updated_lower_bound
                {
                    let overload = task.resource_usage - available_energy % task.resource_usage;
                    context.set_lower_bound(&task.start_variable, updated_lower_bound,
                         create_propagation_explanation_left(context.as_readonly(), (*start, *end), task,
                         overload, &self.parameters))?;
                }
                if available_energy < rs * task.resource_usage
                && context.upper_bound(&task.start_variable) > updated_upper_bound
                {
                    let overload = task.resource_usage - (available_energy + task.resource_usage - 1) % task.resource_usage;
                    context.set_upper_bound(&task.start_variable, updated_upper_bound,
                         create_propagation_explanation_right(context.as_readonly(), (*start, *end), task,
                          overload, &self.parameters))?;
                }
                used_energy += minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
            }
        }
        
        for task in self.parameters.tasks.iter() {
            let intervals_left = generate_left_intervals(context.as_readonly(), &task, &self.parameters);
            for (start, end) in &intervals_left {
                let maximum_energy: i32 = self.parameters.capacity * (end - start);
                let mut used_energy: i32 = 0;
                for task2 in self.parameters.tasks.iter() {
                    used_energy += minimum_interval(context.as_readonly(), (*start, *end), task2) * task2.resource_usage;
                }
                used_energy -= minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                let available_energy = maximum_energy - used_energy;
                let updated_lower_bound = end - available_energy / task.resource_usage;
                let mi = minimum_interval(context.as_readonly(), (*start, *end), task);
                if available_energy < mi * task.resource_usage{
                    let overload = mi * task.resource_usage - available_energy;
                    return Err(create_conflict_explanation(context.as_readonly(), (*start, *end), overload, &self.parameters).into());
                }
                if available_energy < left_shift(context.as_readonly(), (*start, *end), task) * task.resource_usage
                && context.lower_bound(&task.start_variable) < updated_lower_bound
                {
                    let overload = task.resource_usage - available_energy % task.resource_usage;
                    context.set_lower_bound(&task.start_variable, updated_lower_bound,
                         create_propagation_explanation_left(context.as_readonly(), (*start, *end), task,
                         overload, &self.parameters))?;
                }
            }
            let intervals_right = generate_right_intervals(context.as_readonly(), &task, &self.parameters);
            for (start, end) in &intervals_right {
                let maximum_energy: i32 = self.parameters.capacity * (end - start);
                let mut used_energy: i32 = 0;
                for task in self.parameters.tasks.iter() {
                    used_energy += minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                }
                used_energy -= minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                let available_energy = maximum_energy - used_energy;
                let updated_upper_bound = start + (available_energy + task.resource_usage - 1) / task.resource_usage - task.processing_time;
                let mi = minimum_interval(context.as_readonly(), (*start, *end), task);
                if available_energy < mi * task.resource_usage{
                    let overload = mi * task.resource_usage - available_energy;
                    return Err(create_conflict_explanation(context.as_readonly(), (*start, *end), overload, &self.parameters).into());
                }
                if available_energy < right_shift(context.as_readonly(), (*start, *end), task) * task.resource_usage
                && context.upper_bound(&task.start_variable) > updated_upper_bound
                {
                    let overload = task.resource_usage - (available_energy + task.resource_usage - 1) % task.resource_usage;
                    context.set_upper_bound(&task.start_variable, updated_upper_bound,
                         create_propagation_explanation_right(context.as_readonly(), (*start, *end), task,
                          overload, &self.parameters))?;
                }
            }
        }

        Ok(())
    }

    fn name(&self) -> &str {
        "EnergeticReasoningKnapsack"
    }
    
    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        let intervals: Vec<(i32, i32)> = generate_all_intervals(context.as_readonly(), &self.parameters);

        for (start, end) in &intervals {
            let maximum_energy: i32 = self.parameters.capacity * (end - start);
            let mut used_energy: i32 = 0;
            for task in self.parameters.tasks.iter() {
                used_energy += minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
            }
            if used_energy > maximum_energy{
                let overload = used_energy - maximum_energy;
                return Err(create_conflict_explanation(context.as_readonly(), (*start, *end), overload, &self.parameters).into());
            }
            for task in self.parameters.tasks.iter() {
                used_energy -= minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                let available_energy = maximum_energy - used_energy;
                let updated_lower_bound = end - available_energy / task.resource_usage;
                let updated_upper_bound = start + (available_energy + task.resource_usage - 1) / task.resource_usage - task.processing_time;
                let ls = left_shift(context.as_readonly(), (*start, *end), task);
                let rs = right_shift(context.as_readonly(), (*start, *end), task);
                if available_energy < ls * task.resource_usage
                && context.lower_bound(&task.start_variable) < updated_lower_bound
                {
                    let overload = task.resource_usage - available_energy % task.resource_usage;
                    context.set_lower_bound(&task.start_variable, updated_lower_bound,
                         create_propagation_explanation_left(context.as_readonly(), (*start, *end), task,
                         overload, &self.parameters))?;
                }
                if available_energy < rs * task.resource_usage
                && context.upper_bound(&task.start_variable) > updated_upper_bound
                {
                    let overload = task.resource_usage - (available_energy + task.resource_usage - 1) % task.resource_usage;
                    context.set_upper_bound(&task.start_variable, updated_upper_bound,
                         create_propagation_explanation_right(context.as_readonly(), (*start, *end), task,
                          overload, &self.parameters))?;
                }
                used_energy += minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
            }
        }
        
        for task in self.parameters.tasks.iter() {
            let intervals_left = generate_left_intervals(context.as_readonly(), &task, &self.parameters);
            for (start, end) in &intervals_left {
                let maximum_energy: i32 = self.parameters.capacity * (end - start);
                let mut used_energy: i32 = 0;
                for task2 in self.parameters.tasks.iter() {
                    used_energy += minimum_interval(context.as_readonly(), (*start, *end), task2) * task2.resource_usage;
                }
                used_energy -= minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                let available_energy = maximum_energy - used_energy;
                let updated_lower_bound = end - available_energy / task.resource_usage;
                let mi = minimum_interval(context.as_readonly(), (*start, *end), task);
                if available_energy < mi * task.resource_usage{
                    let overload = mi * task.resource_usage - available_energy;
                    return Err(create_conflict_explanation(context.as_readonly(), (*start, *end), overload, &self.parameters).into());
                }
                if available_energy < left_shift(context.as_readonly(), (*start, *end), task) * task.resource_usage
                && context.lower_bound(&task.start_variable) < updated_lower_bound
                {
                    let overload = task.resource_usage - available_energy % task.resource_usage;
                    context.set_lower_bound(&task.start_variable, updated_lower_bound,
                         create_propagation_explanation_left(context.as_readonly(), (*start, *end), task,
                         overload, &self.parameters))?;
                }
            }
            let intervals_right = generate_right_intervals(context.as_readonly(), &task, &self.parameters);
            for (start, end) in &intervals_right {
                let maximum_energy: i32 = self.parameters.capacity * (end - start);
                let mut used_energy: i32 = 0;
                for task in self.parameters.tasks.iter() {
                    used_energy += minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                }
                used_energy -= minimum_interval(context.as_readonly(), (*start, *end), task) * task.resource_usage;
                let available_energy = maximum_energy - used_energy;
                let updated_upper_bound = start + (available_energy + task.resource_usage - 1) / task.resource_usage - task.processing_time;
                let mi = minimum_interval(context.as_readonly(), (*start, *end), task);
                if available_energy < mi * task.resource_usage{
                    let overload = mi * task.resource_usage - available_energy;
                    return Err(create_conflict_explanation(context.as_readonly(), (*start, *end), overload, &self.parameters).into());
                }
                if available_energy < right_shift(context.as_readonly(), (*start, *end), task) * task.resource_usage
                && context.upper_bound(&task.start_variable) > updated_upper_bound
                {
                    let overload = task.resource_usage - (available_energy + task.resource_usage - 1) % task.resource_usage;
                    context.set_upper_bound(&task.start_variable, updated_upper_bound,
                         create_propagation_explanation_right(context.as_readonly(), (*start, *end), task,
                          overload, &self.parameters))?;
                }
            }
        }

        Ok(())
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        register_tasks(&self.parameters.tasks, context, false);

        Ok(())
    }

    fn log_statistics(&self, _statistic_logger: StatisticLogger) {
        _statistic_logger.log_statistic(Statistics{
            no_energy: unsafe { NO_ENERGY },
            no_removal: unsafe { NO_REMOVAL },
            no_change: unsafe { NO_CHANGE },
            total_energy: unsafe { TOTAL_ENERGY },
            total_explanations: unsafe { TOTAL_EXPLANATIONS }, 
            normalized_energy: unsafe { NORMALIZED_ENERGY }});
    }
}